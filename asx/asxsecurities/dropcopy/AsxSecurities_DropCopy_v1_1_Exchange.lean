import Wire

/-!
# Australian Securities Exchange Drop Copy v1.1, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxsecuritiesDropcopyFixV11Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  senderLocationID : Option (Terminated 1)  -- tag 142
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [49, 52, 50] record.senderLocationID,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[49, 52, 50]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]], [[49, 49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderLocationID ← readOptional [49, 52, 50] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, senderLocationID, sendingTime, possDupFlag, possResend, origSendingTime, applVerID }

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
  have senderLocationID := readOptional_part [49, 52, 50] record.senderLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, senderLocationID, sendingTime, possDupFlag, possResend, origSendingTime, applVerID, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  defaultApplVerID : Terminated 1  -- tag 1137
  defaultCstmApplVerID : Option (Terminated 1)  -- tag 1408

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [49, 52, 48, 56] record.defaultCstmApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]], [[49, 49, 51, 55]], [[49, 52, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let defaultCstmApplVerID ← readOptional [49, 52, 48, 56] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, username, password, defaultApplVerID, defaultCstmApplVerID }

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
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultCstmApplVerID := readOptional_part [49, 52, 48, 56] record.defaultCstmApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, username, password, defaultApplVerID, defaultCstmApplVerID, some_bind] <;> rfl

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

structure MarketDefinition where
  marketReportID : Terminated 1  -- tag 1394
  marketReqID : Option (Terminated 1)  -- tag 1393
  marketID : Terminated 1  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300
  marketSegmentDesc : Option (Terminated 1)  -- tag 1396

def MarketDefinition.parts (record : MarketDefinition) : List Part :=
  [Part.required [49, 51, 57, 52] record.marketReportID,
   Part.optional [49, 51, 57, 51] record.marketReqID,
   Part.required [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID,
   Part.optional [49, 51, 57, 54] record.marketSegmentDesc]

def MarketDefinition.tags : List (List (List UInt8)) :=
  [[[49, 51, 57, 52]], [[49, 51, 57, 51]], [[49, 51, 48, 49]], [[49, 51, 48, 48]], [[49, 51, 57, 54]]]

theorem MarketDefinition.shape (record : MarketDefinition) : record.parts.map Part.tags = MarketDefinition.tags := rfl

def MarketDefinition.decode (tokens : List Token) : Option MarketDefinition := do
  let marketReportID ← readRequired [49, 51, 57, 52] tokens
  let marketReqID ← readOptional [49, 51, 57, 51] tokens
  let marketID ← readRequired [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  let marketSegmentDesc ← readOptional [49, 51, 57, 54] tokens
  pure { marketReportID, marketReqID, marketID, marketSegmentID, marketSegmentDesc }

theorem MarketDefinition.decode_agrees (record : MarketDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDefinition.decode tokens = some record := by
  have distinct : MarketDefinition.tags.flatten.Nodup := by decide +kernel
  have marketReportID := readRequired_part [49, 51, 57, 52] record.marketReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketReqID := readOptional_part [49, 51, 57, 51] record.marketReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketSegmentDesc := readOptional_part [49, 51, 57, 54] record.marketSegmentDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [MarketDefinition.decode, marketReportID, marketReqID, marketID, marketSegmentID, marketSegmentDesc, some_bind] <;> rfl

structure NoOrdTypeRules where
  ordType : Terminated 1  -- tag 40

def NoOrdTypeRules.parts (record : NoOrdTypeRules) : List Part :=
  [Part.required [52, 48] record.ordType]

def NoOrdTypeRules.tags : List (List (List UInt8)) :=
  [[[52, 48]]]

theorem NoOrdTypeRules.shape (record : NoOrdTypeRules) : record.parts.map Part.tags = NoOrdTypeRules.tags := rfl

def NoOrdTypeRules.decode (tokens : List Token) : Option NoOrdTypeRules := do
  let ordType ← readRequired [52, 48] tokens
  pure { ordType }

theorem NoOrdTypeRules.decode_agrees (record : NoOrdTypeRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrdTypeRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrdTypeRules.decode tokens = some record := by
  have distinct : NoOrdTypeRules.tags.flatten.Nodup := by decide +kernel
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoOrdTypeRules.decode, ordType, some_bind] <;> rfl

def NoOrdTypeRules.members : List (List UInt8) := NoOrdTypeRules.tags.flatten

def NoOrdTypeRules.encode (entry : NoOrdTypeRules) : List Token := encodeParts entry.parts

theorem NoOrdTypeRules.decode_encode (entry : NoOrdTypeRules) : NoOrdTypeRules.decode entry.encode = some entry :=
  NoOrdTypeRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrdTypeRules.within (entry : NoOrdTypeRules) : ∀ token ∈ entry.encode, token.tag ∈ NoOrdTypeRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrdTypeRules.shape] at this

theorem NoOrdTypeRules.led (entry : NoOrdTypeRules) : Lead [52, 48] entry.encode :=
  lead_parts [52, 48] entry.ordType _ NoOrdTypeRules.tags.tail rfl (by decide +kernel)

structure NoTimeInForceRules where
  timeInForce : Terminated 1  -- tag 59

def NoTimeInForceRules.parts (record : NoTimeInForceRules) : List Part :=
  [Part.required [53, 57] record.timeInForce]

def NoTimeInForceRules.tags : List (List (List UInt8)) :=
  [[[53, 57]]]

theorem NoTimeInForceRules.shape (record : NoTimeInForceRules) : record.parts.map Part.tags = NoTimeInForceRules.tags := rfl

def NoTimeInForceRules.decode (tokens : List Token) : Option NoTimeInForceRules := do
  let timeInForce ← readRequired [53, 57] tokens
  pure { timeInForce }

theorem NoTimeInForceRules.decode_agrees (record : NoTimeInForceRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTimeInForceRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTimeInForceRules.decode tokens = some record := by
  have distinct : NoTimeInForceRules.tags.flatten.Nodup := by decide +kernel
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTimeInForceRules.decode, timeInForce, some_bind] <;> rfl

def NoTimeInForceRules.members : List (List UInt8) := NoTimeInForceRules.tags.flatten

def NoTimeInForceRules.encode (entry : NoTimeInForceRules) : List Token := encodeParts entry.parts

theorem NoTimeInForceRules.decode_encode (entry : NoTimeInForceRules) : NoTimeInForceRules.decode entry.encode = some entry :=
  NoTimeInForceRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTimeInForceRules.within (entry : NoTimeInForceRules) : ∀ token ∈ entry.encode, token.tag ∈ NoTimeInForceRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTimeInForceRules.shape] at this

theorem NoTimeInForceRules.led (entry : NoTimeInForceRules) : Lead [53, 57] entry.encode :=
  lead_parts [53, 57] entry.timeInForce _ NoTimeInForceRules.tags.tail rfl (by decide +kernel)

structure NoMatchRules where
  matchAlgorithm : Terminated 1  -- tag 1142
  matchType : Option (Terminated 1)  -- tag 574
  sessionStateTypeNumber : Option (Terminated 1)  -- tag 28032

def NoMatchRules.parts (record : NoMatchRules) : List Part :=
  [Part.required [49, 49, 52, 50] record.matchAlgorithm,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [50, 56, 48, 51, 50] record.sessionStateTypeNumber]

def NoMatchRules.tags : List (List (List UInt8)) :=
  [[[49, 49, 52, 50]], [[53, 55, 52]], [[50, 56, 48, 51, 50]]]

theorem NoMatchRules.shape (record : NoMatchRules) : record.parts.map Part.tags = NoMatchRules.tags := rfl

def NoMatchRules.decode (tokens : List Token) : Option NoMatchRules := do
  let matchAlgorithm ← readRequired [49, 49, 52, 50] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let sessionStateTypeNumber ← readOptional [50, 56, 48, 51, 50] tokens
  pure { matchAlgorithm, matchType, sessionStateTypeNumber }

theorem NoMatchRules.decode_agrees (record : NoMatchRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchRules.decode tokens = some record := by
  have distinct : NoMatchRules.tags.flatten.Nodup := by decide +kernel
  have matchAlgorithm := readRequired_part [49, 49, 52, 50] record.matchAlgorithm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionStateTypeNumber := readOptional_part [50, 56, 48, 51, 50] record.sessionStateTypeNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoMatchRules.decode, matchAlgorithm, matchType, sessionStateTypeNumber, some_bind] <;> rfl

def NoMatchRules.members : List (List UInt8) := NoMatchRules.tags.flatten

def NoMatchRules.encode (entry : NoMatchRules) : List Token := encodeParts entry.parts

theorem NoMatchRules.decode_encode (entry : NoMatchRules) : NoMatchRules.decode entry.encode = some entry :=
  NoMatchRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchRules.within (entry : NoMatchRules) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchRules.shape] at this

theorem NoMatchRules.led (entry : NoMatchRules) : Lead [49, 49, 52, 50] entry.encode :=
  lead_parts [49, 49, 52, 50] entry.matchAlgorithm _ NoMatchRules.tags.tail rfl (by decide +kernel)

structure NoTradingSessions where
  tradingSessionID : Terminated 1  -- tag 336
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  tradingSessionDesc : Option (Terminated 1)  -- tag 1326
  tradSesStatus : Option (Terminated 1)  -- tag 340
  noOrdTypeRules : List NoOrdTypeRules  -- tag 1237
  noTimeInForceRules : List NoTimeInForceRules  -- tag 1239
  noMatchRules : List NoMatchRules  -- tag 1235

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [49, 51, 50, 54] record.tradingSessionDesc,
   Part.optional [51, 52, 48] record.tradSesStatus,
   Part.group [49, 50, 51, 55] NoOrdTypeRules.members NoOrdTypeRules.encode NoOrdTypeRules.within record.noOrdTypeRules,
   Part.group [49, 50, 51, 57] NoTimeInForceRules.members NoTimeInForceRules.encode NoTimeInForceRules.within record.noTimeInForceRules,
   Part.group [49, 50, 51, 53] NoMatchRules.members NoMatchRules.encode NoMatchRules.within record.noMatchRules]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]], [[54, 50, 53]], [[49, 51, 50, 54]], [[51, 52, 48]], [49, 50, 51, 55] :: NoOrdTypeRules.members, [49, 50, 51, 57] :: NoTimeInForceRules.members, [49, 50, 51, 53] :: NoMatchRules.members]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let tradingSessionDesc ← readOptional [49, 51, 50, 54] tokens
  let tradSesStatus ← readOptional [51, 52, 48] tokens
  let noOrdTypeRules ← readGroup [49, 50, 51, 55] [52, 48] NoOrdTypeRules.members NoOrdTypeRules.decode tokens
  let noTimeInForceRules ← readGroup [49, 50, 51, 57] [53, 57] NoTimeInForceRules.members NoTimeInForceRules.decode tokens
  let noMatchRules ← readGroup [49, 50, 51, 53] [49, 49, 52, 50] NoMatchRules.members NoMatchRules.decode tokens
  pure { tradingSessionID, tradingSessionSubID, tradingSessionDesc, tradSesStatus, noOrdTypeRules, noTimeInForceRules, noMatchRules }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingSessionDesc := readOptional_part [49, 51, 50, 54] record.tradingSessionDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradSesStatus := readOptional_part [51, 52, 48] record.tradSesStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noOrdTypeRules := readGroup_part [49, 50, 51, 55] [52, 48] NoOrdTypeRules.members NoOrdTypeRules.encode NoOrdTypeRules.within NoOrdTypeRules.decode NoOrdTypeRules.decode_encode NoOrdTypeRules.led record.noOrdTypeRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noTimeInForceRules := readGroup_part [49, 50, 51, 57] [53, 57] NoTimeInForceRules.members NoTimeInForceRules.encode NoTimeInForceRules.within NoTimeInForceRules.decode NoTimeInForceRules.decode_encode NoTimeInForceRules.led record.noTimeInForceRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noMatchRules := readGroup_part [49, 50, 51, 53] [49, 49, 52, 50] NoMatchRules.members NoMatchRules.encode NoMatchRules.within NoMatchRules.decode NoMatchRules.decode_encode NoMatchRules.led record.noMatchRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, tradingSessionSubID, tradingSessionDesc, tradSesStatus, noOrdTypeRules, noTimeInForceRules, noMatchRules, some_bind] <;> rfl

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

structure TradingSessionList where
  tradSesReqID : Terminated 1  -- tag 335
  noTradingSessions : List NoTradingSessions  -- tag 386

def TradingSessionList.parts (record : TradingSessionList) : List Part :=
  [Part.required [51, 51, 53] record.tradSesReqID,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions]

def TradingSessionList.tags : List (List (List UInt8)) :=
  [[[51, 51, 53]], [51, 56, 54] :: NoTradingSessions.members]

theorem TradingSessionList.shape (record : TradingSessionList) : record.parts.map Part.tags = TradingSessionList.tags := rfl

def TradingSessionList.decode (tokens : List Token) : Option TradingSessionList := do
  let tradSesReqID ← readRequired [51, 51, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  pure { tradSesReqID, noTradingSessions }

theorem TradingSessionList.decode_agrees (record : TradingSessionList) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionList.decode tokens = some record := by
  have distinct : TradingSessionList.tags.flatten.Nodup := by decide +kernel
  have tradSesReqID := readRequired_part [51, 51, 53] record.tradSesReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [TradingSessionList.decode, tradSesReqID, noTradingSessions, some_bind] <;> rfl

structure NoSecurityAltID where
  securityAltID : Terminated 1  -- tag 455
  securityAltIDSource : Option (Terminated 1)  -- tag 456

def NoSecurityAltID.parts (record : NoSecurityAltID) : List Part :=
  [Part.required [52, 53, 53] record.securityAltID,
   Part.optional [52, 53, 54] record.securityAltIDSource]

def NoSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 53]], [[52, 53, 54]]]

theorem NoSecurityAltID.shape (record : NoSecurityAltID) : record.parts.map Part.tags = NoSecurityAltID.tags := rfl

def NoSecurityAltID.decode (tokens : List Token) : Option NoSecurityAltID := do
  let securityAltID ← readRequired [52, 53, 53] tokens
  let securityAltIDSource ← readOptional [52, 53, 54] tokens
  pure { securityAltID, securityAltIDSource }

theorem NoSecurityAltID.decode_agrees (record : NoSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSecurityAltID.decode tokens = some record := by
  have distinct : NoSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have securityAltID := readRequired_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityAltIDSource := readOptional_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoSecurityAltID.decode, securityAltID, securityAltIDSource, some_bind] <;> rfl

def NoSecurityAltID.members : List (List UInt8) := NoSecurityAltID.tags.flatten

def NoSecurityAltID.encode (entry : NoSecurityAltID) : List Token := encodeParts entry.parts

theorem NoSecurityAltID.decode_encode (entry : NoSecurityAltID) : NoSecurityAltID.decode entry.encode = some entry :=
  NoSecurityAltID.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSecurityAltID.within (entry : NoSecurityAltID) : ∀ token ∈ entry.encode, token.tag ∈ NoSecurityAltID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSecurityAltID.shape] at this

theorem NoSecurityAltID.led (entry : NoSecurityAltID) : Lead [52, 53, 53] entry.encode :=
  lead_parts [52, 53, 53] entry.securityAltID _ NoSecurityAltID.tags.tail rfl (by decide +kernel)

structure NoEvents where
  eventType : Terminated 1  -- tag 865
  eventDate : Option (Terminated 1)  -- tag 866
  eventTime : Option (Terminated 1)  -- tag 1145

def NoEvents.parts (record : NoEvents) : List Part :=
  [Part.required [56, 54, 53] record.eventType,
   Part.optional [56, 54, 54] record.eventDate,
   Part.optional [49, 49, 52, 53] record.eventTime]

def NoEvents.tags : List (List (List UInt8)) :=
  [[[56, 54, 53]], [[56, 54, 54]], [[49, 49, 52, 53]]]

theorem NoEvents.shape (record : NoEvents) : record.parts.map Part.tags = NoEvents.tags := rfl

def NoEvents.decode (tokens : List Token) : Option NoEvents := do
  let eventType ← readRequired [56, 54, 53] tokens
  let eventDate ← readOptional [56, 54, 54] tokens
  let eventTime ← readOptional [49, 49, 52, 53] tokens
  pure { eventType, eventDate, eventTime }

theorem NoEvents.decode_agrees (record : NoEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEvents.decode tokens = some record := by
  have distinct : NoEvents.tags.flatten.Nodup := by decide +kernel
  have eventType := readRequired_part [56, 54, 53] record.eventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventDate := readOptional_part [56, 54, 54] record.eventDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eventTime := readOptional_part [49, 49, 52, 53] record.eventTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoEvents.decode, eventType, eventDate, eventTime, some_bind] <;> rfl

def NoEvents.members : List (List UInt8) := NoEvents.tags.flatten

def NoEvents.encode (entry : NoEvents) : List Token := encodeParts entry.parts

theorem NoEvents.decode_encode (entry : NoEvents) : NoEvents.decode entry.encode = some entry :=
  NoEvents.decode_agrees entry _ (fun _ _ => rfl)

theorem NoEvents.within (entry : NoEvents) : ∀ token ∈ entry.encode, token.tag ∈ NoEvents.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoEvents.shape] at this

theorem NoEvents.led (entry : NoEvents) : Lead [56, 54, 53] entry.encode :=
  lead_parts [56, 54, 53] entry.eventType _ NoEvents.tags.tail rfl (by decide +kernel)

structure NoTickRules where
  startTickPriceRange : Terminated 1  -- tag 1206
  endTickPriceRange : Option (Terminated 1)  -- tag 1207
  tickIncrement : Option (Terminated 1)  -- tag 1208

def NoTickRules.parts (record : NoTickRules) : List Part :=
  [Part.required [49, 50, 48, 54] record.startTickPriceRange,
   Part.optional [49, 50, 48, 55] record.endTickPriceRange,
   Part.optional [49, 50, 48, 56] record.tickIncrement]

def NoTickRules.tags : List (List (List UInt8)) :=
  [[[49, 50, 48, 54]], [[49, 50, 48, 55]], [[49, 50, 48, 56]]]

theorem NoTickRules.shape (record : NoTickRules) : record.parts.map Part.tags = NoTickRules.tags := rfl

def NoTickRules.decode (tokens : List Token) : Option NoTickRules := do
  let startTickPriceRange ← readRequired [49, 50, 48, 54] tokens
  let endTickPriceRange ← readOptional [49, 50, 48, 55] tokens
  let tickIncrement ← readOptional [49, 50, 48, 56] tokens
  pure { startTickPriceRange, endTickPriceRange, tickIncrement }

theorem NoTickRules.decode_agrees (record : NoTickRules) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTickRules.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTickRules.decode tokens = some record := by
  have distinct : NoTickRules.tags.flatten.Nodup := by decide +kernel
  have startTickPriceRange := readRequired_part [49, 50, 48, 54] record.startTickPriceRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have endTickPriceRange := readOptional_part [49, 50, 48, 55] record.endTickPriceRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tickIncrement := readOptional_part [49, 50, 48, 56] record.tickIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoTickRules.decode, startTickPriceRange, endTickPriceRange, tickIncrement, some_bind] <;> rfl

def NoTickRules.members : List (List UInt8) := NoTickRules.tags.flatten

def NoTickRules.encode (entry : NoTickRules) : List Token := encodeParts entry.parts

theorem NoTickRules.decode_encode (entry : NoTickRules) : NoTickRules.decode entry.encode = some entry :=
  NoTickRules.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTickRules.within (entry : NoTickRules) : ∀ token ∈ entry.encode, token.tag ∈ NoTickRules.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTickRules.shape] at this

theorem NoTickRules.led (entry : NoTickRules) : Lead [49, 50, 48, 54] entry.encode :=
  lead_parts [49, 50, 48, 54] entry.startTickPriceRange _ NoTickRules.tags.tail rfl (by decide +kernel)

structure NoUnderlyingSecurityAltID where
  underlyingSecurityAltID : Terminated 1  -- tag 458
  underlyingSecurityAltIDSource : Option (Terminated 1)  -- tag 459

def NoUnderlyingSecurityAltID.parts (record : NoUnderlyingSecurityAltID) : List Part :=
  [Part.required [52, 53, 56] record.underlyingSecurityAltID,
   Part.optional [52, 53, 57] record.underlyingSecurityAltIDSource]

def NoUnderlyingSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 56]], [[52, 53, 57]]]

theorem NoUnderlyingSecurityAltID.shape (record : NoUnderlyingSecurityAltID) : record.parts.map Part.tags = NoUnderlyingSecurityAltID.tags := rfl

def NoUnderlyingSecurityAltID.decode (tokens : List Token) : Option NoUnderlyingSecurityAltID := do
  let underlyingSecurityAltID ← readRequired [52, 53, 56] tokens
  let underlyingSecurityAltIDSource ← readOptional [52, 53, 57] tokens
  pure { underlyingSecurityAltID, underlyingSecurityAltIDSource }

theorem NoUnderlyingSecurityAltID.decode_agrees (record : NoUnderlyingSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUnderlyingSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUnderlyingSecurityAltID.decode tokens = some record := by
  have distinct : NoUnderlyingSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have underlyingSecurityAltID := readRequired_part [52, 53, 56] record.underlyingSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have underlyingSecurityAltIDSource := readOptional_part [52, 53, 57] record.underlyingSecurityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoUnderlyingSecurityAltID.decode, underlyingSecurityAltID, underlyingSecurityAltIDSource, some_bind] <;> rfl

def NoUnderlyingSecurityAltID.members : List (List UInt8) := NoUnderlyingSecurityAltID.tags.flatten

def NoUnderlyingSecurityAltID.encode (entry : NoUnderlyingSecurityAltID) : List Token := encodeParts entry.parts

theorem NoUnderlyingSecurityAltID.decode_encode (entry : NoUnderlyingSecurityAltID) : NoUnderlyingSecurityAltID.decode entry.encode = some entry :=
  NoUnderlyingSecurityAltID.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUnderlyingSecurityAltID.within (entry : NoUnderlyingSecurityAltID) : ∀ token ∈ entry.encode, token.tag ∈ NoUnderlyingSecurityAltID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUnderlyingSecurityAltID.shape] at this

theorem NoUnderlyingSecurityAltID.led (entry : NoUnderlyingSecurityAltID) : Lead [52, 53, 56] entry.encode :=
  lead_parts [52, 53, 56] entry.underlyingSecurityAltID _ NoUnderlyingSecurityAltID.tags.tail rfl (by decide +kernel)

structure NoUnderlyings where
  underlyingSymbol : Terminated 1  -- tag 311
  underlyingSecurityID : Option (Terminated 1)  -- tag 309
  underlyingSecurityIDSource : Option (Terminated 1)  -- tag 305
  noUnderlyingSecurityAltID : List NoUnderlyingSecurityAltID  -- tag 457

def NoUnderlyings.parts (record : NoUnderlyings) : List Part :=
  [Part.required [51, 49, 49] record.underlyingSymbol,
   Part.optional [51, 48, 57] record.underlyingSecurityID,
   Part.optional [51, 48, 53] record.underlyingSecurityIDSource,
   Part.group [52, 53, 55] NoUnderlyingSecurityAltID.members NoUnderlyingSecurityAltID.encode NoUnderlyingSecurityAltID.within record.noUnderlyingSecurityAltID]

def NoUnderlyings.tags : List (List (List UInt8)) :=
  [[[51, 49, 49]], [[51, 48, 57]], [[51, 48, 53]], [52, 53, 55] :: NoUnderlyingSecurityAltID.members]

theorem NoUnderlyings.shape (record : NoUnderlyings) : record.parts.map Part.tags = NoUnderlyings.tags := rfl

def NoUnderlyings.decode (tokens : List Token) : Option NoUnderlyings := do
  let underlyingSymbol ← readRequired [51, 49, 49] tokens
  let underlyingSecurityID ← readOptional [51, 48, 57] tokens
  let underlyingSecurityIDSource ← readOptional [51, 48, 53] tokens
  let noUnderlyingSecurityAltID ← readGroup [52, 53, 55] [52, 53, 56] NoUnderlyingSecurityAltID.members NoUnderlyingSecurityAltID.decode tokens
  pure { underlyingSymbol, underlyingSecurityID, underlyingSecurityIDSource, noUnderlyingSecurityAltID }

theorem NoUnderlyings.decode_agrees (record : NoUnderlyings) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUnderlyings.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUnderlyings.decode tokens = some record := by
  have distinct : NoUnderlyings.tags.flatten.Nodup := by decide +kernel
  have underlyingSymbol := readRequired_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have underlyingSecurityID := readOptional_part [51, 48, 57] record.underlyingSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have underlyingSecurityIDSource := readOptional_part [51, 48, 53] record.underlyingSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noUnderlyingSecurityAltID := readGroup_part [52, 53, 55] [52, 53, 56] NoUnderlyingSecurityAltID.members NoUnderlyingSecurityAltID.encode NoUnderlyingSecurityAltID.within NoUnderlyingSecurityAltID.decode NoUnderlyingSecurityAltID.decode_encode NoUnderlyingSecurityAltID.led record.noUnderlyingSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoUnderlyings.decode, underlyingSymbol, underlyingSecurityID, underlyingSecurityIDSource, noUnderlyingSecurityAltID, some_bind] <;> rfl

def NoUnderlyings.members : List (List UInt8) := NoUnderlyings.tags.flatten

def NoUnderlyings.encode (entry : NoUnderlyings) : List Token := encodeParts entry.parts

theorem NoUnderlyings.decode_encode (entry : NoUnderlyings) : NoUnderlyings.decode entry.encode = some entry :=
  NoUnderlyings.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUnderlyings.within (entry : NoUnderlyings) : ∀ token ∈ entry.encode, token.tag ∈ NoUnderlyings.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUnderlyings.shape] at this

theorem NoUnderlyings.led (entry : NoUnderlyings) : Lead [51, 49, 49] entry.encode :=
  lead_parts [51, 49, 49] entry.underlyingSymbol _ NoUnderlyings.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSource : Option (Terminated 1)  -- tag 603
  legRatioQty : Option (Terminated 1)  -- tag 623
  legSide : Option (Terminated 1)  -- tag 624
  legAliasName : Option (Terminated 1)  -- tag 24128

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSource,
   Part.optional [54, 50, 51] record.legRatioQty,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [50, 52, 49, 50, 56] record.legAliasName]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 50, 51]], [[54, 50, 52]], [[50, 52, 49, 50, 56]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSource ← readOptional [54, 48, 51] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legAliasName ← readOptional [50, 52, 49, 50, 56] tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legRatioQty, legSide, legAliasName }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSecurityID := readOptional_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSecurityIDSource := readOptional_part [54, 48, 51] record.legSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legAliasName := readOptional_part [50, 52, 49, 50, 56] record.legAliasName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legRatioQty, legSide, legAliasName, some_bind] <;> rfl

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

structure NoInstrAttrib where
  instrAttribType : Terminated 1  -- tag 871
  instrAttribValue : Option (Terminated 1)  -- tag 872

def NoInstrAttrib.parts (record : NoInstrAttrib) : List Part :=
  [Part.required [56, 55, 49] record.instrAttribType,
   Part.optional [56, 55, 50] record.instrAttribValue]

def NoInstrAttrib.tags : List (List (List UInt8)) :=
  [[[56, 55, 49]], [[56, 55, 50]]]

theorem NoInstrAttrib.shape (record : NoInstrAttrib) : record.parts.map Part.tags = NoInstrAttrib.tags := rfl

def NoInstrAttrib.decode (tokens : List Token) : Option NoInstrAttrib := do
  let instrAttribType ← readRequired [56, 55, 49] tokens
  let instrAttribValue ← readOptional [56, 55, 50] tokens
  pure { instrAttribType, instrAttribValue }

theorem NoInstrAttrib.decode_agrees (record : NoInstrAttrib) (tokens : List Token)
    (agrees : ∀ tags ∈ NoInstrAttrib.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoInstrAttrib.decode tokens = some record := by
  have distinct : NoInstrAttrib.tags.flatten.Nodup := by decide +kernel
  have instrAttribType := readRequired_part [56, 55, 49] record.instrAttribType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have instrAttribValue := readOptional_part [56, 55, 50] record.instrAttribValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoInstrAttrib.decode, instrAttribType, instrAttribValue, some_bind] <;> rfl

def NoInstrAttrib.members : List (List UInt8) := NoInstrAttrib.tags.flatten

def NoInstrAttrib.encode (entry : NoInstrAttrib) : List Token := encodeParts entry.parts

theorem NoInstrAttrib.decode_encode (entry : NoInstrAttrib) : NoInstrAttrib.decode entry.encode = some entry :=
  NoInstrAttrib.decode_agrees entry _ (fun _ _ => rfl)

theorem NoInstrAttrib.within (entry : NoInstrAttrib) : ∀ token ∈ entry.encode, token.tag ∈ NoInstrAttrib.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoInstrAttrib.shape] at this

theorem NoInstrAttrib.led (entry : NoInstrAttrib) : Lead [56, 55, 49] entry.encode :=
  lead_parts [56, 55, 49] entry.instrAttribType _ NoInstrAttrib.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  cFICode : Option (Terminated 1)  -- tag 461
  maturityDate : Option (Terminated 1)  -- tag 541
  securityStatus : Option (Terminated 1)  -- tag 965
  strikePrice : Option (Terminated 1)  -- tag 202
  strikePricePrecision : Option (Terminated 1)  -- tag 2577
  contractMultiplier : Option (Terminated 1)  -- tag 231
  settlMethod : Option (Terminated 1)  -- tag 1193
  exerciseStyle : Option (Terminated 1)  -- tag 1194
  putOrCall : Option (Terminated 1)  -- tag 201
  securityDesc : Option (Terminated 1)  -- tag 107
  issuer : Option (Terminated 1)  -- tag 106
  noEvents : List NoEvents  -- tag 864
  noTickRules : List NoTickRules  -- tag 1205
  roundLot : Option (Terminated 1)  -- tag 561
  currency : Option (Terminated 1)  -- tag 15
  noUnderlyings : List NoUnderlyings  -- tag 711
  noLegs : List NoLegs  -- tag 555
  noInstrAttrib : List NoInstrAttrib  -- tag 870
  factor : Option (Terminated 1)  -- tag 228
  couponFrequencyPeriod : Option (Terminated 1)  -- tag 1948
  couponRate : Option (Terminated 1)  -- tag 223
  issueDate : Option (Terminated 1)  -- tag 225
  couponPaymentDate : Option (Terminated 1)  -- tag 224
  exDate : Option (Terminated 1)  -- tag 230
  settlType : Option (Terminated 1)  -- tag 63
  settlDate : Option (Terminated 1)  -- tag 64
  instrumentPricePrecision : Option (Terminated 1)  -- tag 2567
  datedDate : Option (Terminated 1)  -- tag 873
  couponDayCount : Option (Terminated 1)  -- tag 1950
  dividendYield : Option (Terminated 1)  -- tag 1380
  roundingDirection : Option (Terminated 1)  -- tag 468
  aliasName : Option (Terminated 1)  -- tag 24110
  corporateActionCode : Option (Terminated 1)  -- tag 24113
  corporateActionCodeType : Option (Terminated 1)  -- tag 24114
  aSXSecurityType : Option (Terminated 1)  -- tag 24115
  aSXInstrumentClass : Option (Terminated 1)  -- tag 24116
  linkedCommodity : Option (Terminated 1)  -- tag 24117
  upperLevelInstrument : Option (Terminated 1)  -- tag 24118
  upperLevelInstrumentCode : Option (Terminated 1)  -- tag 24119
  accruedInterestRounding : Option (Terminated 1)  -- tag 24120
  cleanPriceRounding : Option (Terminated 1)  -- tag 24121
  yieldConvention : Option (Terminated 1)  -- tag 24122
  refSettlementDate : Option (Terminated 1)  -- tag 24123
  iTRminVal : Option (Terminated 1)  -- tag 24124
  extInfoInstrClass : Option (Terminated 1)  -- tag 24125
  foreignOwnFlag : Option (Terminated 1)  -- tag 24126
  practiseSec : Option (Terminated 1)  -- tag 24127

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [52, 54, 49] record.cFICode,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [57, 54, 53] record.securityStatus,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 53, 55, 55] record.strikePricePrecision,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [49, 49, 57, 51] record.settlMethod,
   Part.optional [49, 49, 57, 52] record.exerciseStyle,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [49, 48, 54] record.issuer,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.group [49, 50, 48, 53] NoTickRules.members NoTickRules.encode NoTickRules.within record.noTickRules,
   Part.optional [53, 54, 49] record.roundLot,
   Part.optional [49, 53] record.currency,
   Part.group [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within record.noUnderlyings,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.group [56, 55, 48] NoInstrAttrib.members NoInstrAttrib.encode NoInstrAttrib.within record.noInstrAttrib,
   Part.optional [50, 50, 56] record.factor,
   Part.optional [49, 57, 52, 56] record.couponFrequencyPeriod,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [50, 50, 52] record.couponPaymentDate,
   Part.optional [50, 51, 48] record.exDate,
   Part.optional [54, 51] record.settlType,
   Part.optional [54, 52] record.settlDate,
   Part.optional [50, 53, 54, 55] record.instrumentPricePrecision,
   Part.optional [56, 55, 51] record.datedDate,
   Part.optional [49, 57, 53, 48] record.couponDayCount,
   Part.optional [49, 51, 56, 48] record.dividendYield,
   Part.optional [52, 54, 56] record.roundingDirection,
   Part.optional [50, 52, 49, 49, 48] record.aliasName,
   Part.optional [50, 52, 49, 49, 51] record.corporateActionCode,
   Part.optional [50, 52, 49, 49, 52] record.corporateActionCodeType,
   Part.optional [50, 52, 49, 49, 53] record.aSXSecurityType,
   Part.optional [50, 52, 49, 49, 54] record.aSXInstrumentClass,
   Part.optional [50, 52, 49, 49, 55] record.linkedCommodity,
   Part.optional [50, 52, 49, 49, 56] record.upperLevelInstrument,
   Part.optional [50, 52, 49, 49, 57] record.upperLevelInstrumentCode,
   Part.optional [50, 52, 49, 50, 48] record.accruedInterestRounding,
   Part.optional [50, 52, 49, 50, 49] record.cleanPriceRounding,
   Part.optional [50, 52, 49, 50, 50] record.yieldConvention,
   Part.optional [50, 52, 49, 50, 51] record.refSettlementDate,
   Part.optional [50, 52, 49, 50, 52] record.iTRminVal,
   Part.optional [50, 52, 49, 50, 53] record.extInfoInstrClass,
   Part.optional [50, 52, 49, 50, 54] record.foreignOwnFlag,
   Part.optional [50, 52, 49, 50, 55] record.practiseSec]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[52, 54, 49]], [[53, 52, 49]], [[57, 54, 53]], [[50, 48, 50]], [[50, 53, 55, 55]], [[50, 51, 49]], [[49, 49, 57, 51]], [[49, 49, 57, 52]], [[50, 48, 49]], [[49, 48, 55]], [[49, 48, 54]], [56, 54, 52] :: NoEvents.members, [49, 50, 48, 53] :: NoTickRules.members, [[53, 54, 49]], [[49, 53]], [55, 49, 49] :: NoUnderlyings.members, [53, 53, 53] :: NoLegs.members, [56, 55, 48] :: NoInstrAttrib.members, [[50, 50, 56]], [[49, 57, 52, 56]], [[50, 50, 51]], [[50, 50, 53]], [[50, 50, 52]], [[50, 51, 48]], [[54, 51]], [[54, 52]], [[50, 53, 54, 55]], [[56, 55, 51]], [[49, 57, 53, 48]], [[49, 51, 56, 48]], [[52, 54, 56]], [[50, 52, 49, 49, 48]], [[50, 52, 49, 49, 51]], [[50, 52, 49, 49, 52]], [[50, 52, 49, 49, 53]], [[50, 52, 49, 49, 54]], [[50, 52, 49, 49, 55]], [[50, 52, 49, 49, 56]], [[50, 52, 49, 49, 57]], [[50, 52, 49, 50, 48]], [[50, 52, 49, 50, 49]], [[50, 52, 49, 50, 50]], [[50, 52, 49, 50, 51]], [[50, 52, 49, 50, 52]], [[50, 52, 49, 50, 53]], [[50, 52, 49, 50, 54]], [[50, 52, 49, 50, 55]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let cFICode ← readOptional [52, 54, 49] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let securityStatus ← readOptional [57, 54, 53] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let strikePricePrecision ← readOptional [50, 53, 55, 55] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let settlMethod ← readOptional [49, 49, 57, 51] tokens
  let exerciseStyle ← readOptional [49, 49, 57, 52] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let issuer ← readOptional [49, 48, 54] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let noTickRules ← readGroup [49, 50, 48, 53] [49, 50, 48, 54] NoTickRules.members NoTickRules.decode tokens
  let roundLot ← readOptional [53, 54, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let noUnderlyings ← readGroup [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let noInstrAttrib ← readGroup [56, 55, 48] [56, 55, 49] NoInstrAttrib.members NoInstrAttrib.decode tokens
  let factor ← readOptional [50, 50, 56] tokens
  let couponFrequencyPeriod ← readOptional [49, 57, 52, 56] tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let couponPaymentDate ← readOptional [50, 50, 52] tokens
  let exDate ← readOptional [50, 51, 48] tokens
  let settlType ← readOptional [54, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let instrumentPricePrecision ← readOptional [50, 53, 54, 55] tokens
  let datedDate ← readOptional [56, 55, 51] tokens
  let couponDayCount ← readOptional [49, 57, 53, 48] tokens
  let dividendYield ← readOptional [49, 51, 56, 48] tokens
  let roundingDirection ← readOptional [52, 54, 56] tokens
  let aliasName ← readOptional [50, 52, 49, 49, 48] tokens
  let corporateActionCode ← readOptional [50, 52, 49, 49, 51] tokens
  let corporateActionCodeType ← readOptional [50, 52, 49, 49, 52] tokens
  let aSXSecurityType ← readOptional [50, 52, 49, 49, 53] tokens
  let aSXInstrumentClass ← readOptional [50, 52, 49, 49, 54] tokens
  let linkedCommodity ← readOptional [50, 52, 49, 49, 55] tokens
  let upperLevelInstrument ← readOptional [50, 52, 49, 49, 56] tokens
  let upperLevelInstrumentCode ← readOptional [50, 52, 49, 49, 57] tokens
  let accruedInterestRounding ← readOptional [50, 52, 49, 50, 48] tokens
  let cleanPriceRounding ← readOptional [50, 52, 49, 50, 49] tokens
  let yieldConvention ← readOptional [50, 52, 49, 50, 50] tokens
  let refSettlementDate ← readOptional [50, 52, 49, 50, 51] tokens
  let iTRminVal ← readOptional [50, 52, 49, 50, 52] tokens
  let extInfoInstrClass ← readOptional [50, 52, 49, 50, 53] tokens
  let foreignOwnFlag ← readOptional [50, 52, 49, 50, 54] tokens
  let practiseSec ← readOptional [50, 52, 49, 50, 55] tokens
  pure { symbol, securityID, securityIDSource, noSecurityAltID, cFICode, maturityDate, securityStatus, strikePrice, strikePricePrecision, contractMultiplier, settlMethod, exerciseStyle, putOrCall, securityDesc, issuer, noEvents, noTickRules, roundLot, currency, noUnderlyings, noLegs, noInstrAttrib, factor, couponFrequencyPeriod, couponRate, issueDate, couponPaymentDate, exDate, settlType, settlDate, instrumentPricePrecision, datedDate, couponDayCount, dividendYield, roundingDirection, aliasName, corporateActionCode, corporateActionCodeType, aSXSecurityType, aSXInstrumentClass, linkedCommodity, upperLevelInstrument, upperLevelInstrumentCode, accruedInterestRounding, cleanPriceRounding, yieldConvention, refSettlementDate, iTRminVal, extInfoInstrClass, foreignOwnFlag, practiseSec }

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
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cFICode := readOptional_part [52, 54, 49] record.cFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityStatus := readOptional_part [57, 54, 53] record.securityStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePricePrecision := readOptional_part [50, 53, 55, 55] record.strikePricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have settlMethod := readOptional_part [49, 49, 57, 51] record.settlMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have exerciseStyle := readOptional_part [49, 49, 57, 52] record.exerciseStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have issuer := readOptional_part [49, 48, 54] record.issuer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noTickRules := readGroup_part [49, 50, 48, 53] [49, 50, 48, 54] NoTickRules.members NoTickRules.encode NoTickRules.within NoTickRules.decode NoTickRules.decode_encode NoTickRules.led record.noTickRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have roundLot := readOptional_part [53, 54, 49] record.roundLot tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noUnderlyings := readGroup_part [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within NoUnderlyings.decode NoUnderlyings.decode_encode NoUnderlyings.led record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have noInstrAttrib := readGroup_part [56, 55, 48] [56, 55, 49] NoInstrAttrib.members NoInstrAttrib.encode NoInstrAttrib.within NoInstrAttrib.decode NoInstrAttrib.decode_encode NoInstrAttrib.led record.noInstrAttrib tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have factor := readOptional_part [50, 50, 56] record.factor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have couponFrequencyPeriod := readOptional_part [49, 57, 52, 56] record.couponFrequencyPeriod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have couponPaymentDate := readOptional_part [50, 50, 52] record.couponPaymentDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have exDate := readOptional_part [50, 51, 48] record.exDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have instrumentPricePrecision := readOptional_part [50, 53, 54, 55] record.instrumentPricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have datedDate := readOptional_part [56, 55, 51] record.datedDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have couponDayCount := readOptional_part [49, 57, 53, 48] record.couponDayCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have dividendYield := readOptional_part [49, 51, 56, 48] record.dividendYield tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have roundingDirection := readOptional_part [52, 54, 56] record.roundingDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have aliasName := readOptional_part [50, 52, 49, 49, 48] record.aliasName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have corporateActionCode := readOptional_part [50, 52, 49, 49, 51] record.corporateActionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have corporateActionCodeType := readOptional_part [50, 52, 49, 49, 52] record.corporateActionCodeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have aSXSecurityType := readOptional_part [50, 52, 49, 49, 53] record.aSXSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have aSXInstrumentClass := readOptional_part [50, 52, 49, 49, 54] record.aSXInstrumentClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have linkedCommodity := readOptional_part [50, 52, 49, 49, 55] record.linkedCommodity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have upperLevelInstrument := readOptional_part [50, 52, 49, 49, 56] record.upperLevelInstrument tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have upperLevelInstrumentCode := readOptional_part [50, 52, 49, 49, 57] record.upperLevelInstrumentCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have accruedInterestRounding := readOptional_part [50, 52, 49, 50, 48] record.accruedInterestRounding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have cleanPriceRounding := readOptional_part [50, 52, 49, 50, 49] record.cleanPriceRounding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have yieldConvention := readOptional_part [50, 52, 49, 50, 50] record.yieldConvention tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refSettlementDate := readOptional_part [50, 52, 49, 50, 51] record.refSettlementDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have iTRminVal := readOptional_part [50, 52, 49, 50, 52] record.iTRminVal tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have extInfoInstrClass := readOptional_part [50, 52, 49, 50, 53] record.extInfoInstrClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have foreignOwnFlag := readOptional_part [50, 52, 49, 50, 54] record.foreignOwnFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have practiseSec := readOptional_part [50, 52, 49, 50, 55] record.practiseSec tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, noSecurityAltID, cFICode, maturityDate, securityStatus, strikePrice, strikePricePrecision, contractMultiplier, settlMethod, exerciseStyle, putOrCall, securityDesc, issuer, noEvents, noTickRules, roundLot, currency, noUnderlyings, noLegs, noInstrAttrib, factor, couponFrequencyPeriod, couponRate, issueDate, couponPaymentDate, exDate, settlType, settlDate, instrumentPricePrecision, datedDate, couponDayCount, dividendYield, roundingDirection, aliasName, corporateActionCode, corporateActionCodeType, aSXSecurityType, aSXInstrumentClass, linkedCommodity, upperLevelInstrument, upperLevelInstrumentCode, accruedInterestRounding, cleanPriceRounding, yieldConvention, refSettlementDate, iTRminVal, extInfoInstrClass, foreignOwnFlag, practiseSec, some_bind] <;> rfl

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

structure SecurityList where
  securityReqID : Terminated 1  -- tag 320
  securityRequestResult : Terminated 1  -- tag 560
  totNoRelatedSym : Option (Terminated 1)  -- tag 393
  lastFragment : Option (Terminated 1)  -- tag 893
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300
  noRelatedSym : List NoRelatedSym  -- tag 146

def SecurityList.parts (record : SecurityList) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [53, 54, 48] record.securityRequestResult,
   Part.optional [51, 57, 51] record.totNoRelatedSym,
   Part.optional [56, 57, 51] record.lastFragment,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def SecurityList.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[53, 54, 48]], [[51, 57, 51]], [[56, 57, 51]], [[49, 51, 48, 49]], [[49, 51, 48, 48]], [49, 52, 54] :: NoRelatedSym.members]

theorem SecurityList.shape (record : SecurityList) : record.parts.map Part.tags = SecurityList.tags := rfl

def SecurityList.decode (tokens : List Token) : Option SecurityList := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestResult ← readRequired [53, 54, 48] tokens
  let totNoRelatedSym ← readOptional [51, 57, 51] tokens
  let lastFragment ← readOptional [56, 57, 51] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { securityReqID, securityRequestResult, totNoRelatedSym, lastFragment, marketID, marketSegmentID, noRelatedSym }

theorem SecurityList.decode_agrees (record : SecurityList) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityList.decode tokens = some record := by
  have distinct : SecurityList.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestResult := readRequired_part [53, 54, 48] record.securityRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have totNoRelatedSym := readOptional_part [51, 57, 51] record.totNoRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastFragment := readOptional_part [56, 57, 51] record.lastFragment tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [SecurityList.decode, securityReqID, securityRequestResult, totNoRelatedSym, lastFragment, marketID, marketSegmentID, noRelatedSym, some_bind] <;> rfl

structure NoRelatedSymUpdate where
  listUpdateAction : Terminated 1  -- tag 1324
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  cFICode : Option (Terminated 1)  -- tag 461
  maturityDate : Option (Terminated 1)  -- tag 541
  securityStatus : Option (Terminated 1)  -- tag 965
  strikePrice : Option (Terminated 1)  -- tag 202
  strikePricePrecision : Option (Terminated 1)  -- tag 2577
  contractMultiplier : Option (Terminated 1)  -- tag 231
  settlMethod : Option (Terminated 1)  -- tag 1193
  exerciseStyle : Option (Terminated 1)  -- tag 1194
  putOrCall : Option (Terminated 1)  -- tag 201
  securityDesc : Option (Terminated 1)  -- tag 107
  issuer : Option (Terminated 1)  -- tag 106
  noEvents : List NoEvents  -- tag 864
  noTickRules : List NoTickRules  -- tag 1205
  roundLot : Option (Terminated 1)  -- tag 561
  currency : Option (Terminated 1)  -- tag 15
  noUnderlyings : List NoUnderlyings  -- tag 711
  noLegs : List NoLegs  -- tag 555
  noInstrAttrib : List NoInstrAttrib  -- tag 870
  factor : Option (Terminated 1)  -- tag 228
  couponFrequencyPeriod : Option (Terminated 1)  -- tag 1948
  couponRate : Option (Terminated 1)  -- tag 223
  issueDate : Option (Terminated 1)  -- tag 225
  couponPaymentDate : Option (Terminated 1)  -- tag 224
  exDate : Option (Terminated 1)  -- tag 230
  settlType : Option (Terminated 1)  -- tag 63
  instrumentPricePrecision : Option (Terminated 1)  -- tag 2567
  datedDate : Option (Terminated 1)  -- tag 873
  couponDayCount : Option (Terminated 1)  -- tag 1950
  dividendYield : Option (Terminated 1)  -- tag 1380
  roundingDirection : Option (Terminated 1)  -- tag 468
  aliasName : Option (Terminated 1)  -- tag 24110
  corporateActionCode : Option (Terminated 1)  -- tag 24113
  corporateActionCodeType : Option (Terminated 1)  -- tag 24114
  aSXSecurityType : Option (Terminated 1)  -- tag 24115
  aSXInstrumentClass : Option (Terminated 1)  -- tag 24116
  linkedCommodity : Option (Terminated 1)  -- tag 24117
  upperLevelInstrument : Option (Terminated 1)  -- tag 24118
  upperLevelInstrumentCode : Option (Terminated 1)  -- tag 24119
  accruedInterestRounding : Option (Terminated 1)  -- tag 24120
  cleanPriceRounding : Option (Terminated 1)  -- tag 24121
  yieldConvention : Option (Terminated 1)  -- tag 24122
  refSettlementDate : Option (Terminated 1)  -- tag 24123
  iTRminVal : Option (Terminated 1)  -- tag 24124
  extInfoInstrClass : Option (Terminated 1)  -- tag 24125
  foreignOwnFlag : Option (Terminated 1)  -- tag 24126
  practiseSec : Option (Terminated 1)  -- tag 24127

def NoRelatedSymUpdate.parts (record : NoRelatedSymUpdate) : List Part :=
  [Part.required [49, 51, 50, 52] record.listUpdateAction,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [52, 54, 49] record.cFICode,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [57, 54, 53] record.securityStatus,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 53, 55, 55] record.strikePricePrecision,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [49, 49, 57, 51] record.settlMethod,
   Part.optional [49, 49, 57, 52] record.exerciseStyle,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [49, 48, 54] record.issuer,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.group [49, 50, 48, 53] NoTickRules.members NoTickRules.encode NoTickRules.within record.noTickRules,
   Part.optional [53, 54, 49] record.roundLot,
   Part.optional [49, 53] record.currency,
   Part.group [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within record.noUnderlyings,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.group [56, 55, 48] NoInstrAttrib.members NoInstrAttrib.encode NoInstrAttrib.within record.noInstrAttrib,
   Part.optional [50, 50, 56] record.factor,
   Part.optional [49, 57, 52, 56] record.couponFrequencyPeriod,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [50, 50, 52] record.couponPaymentDate,
   Part.optional [50, 51, 48] record.exDate,
   Part.optional [54, 51] record.settlType,
   Part.optional [50, 53, 54, 55] record.instrumentPricePrecision,
   Part.optional [56, 55, 51] record.datedDate,
   Part.optional [49, 57, 53, 48] record.couponDayCount,
   Part.optional [49, 51, 56, 48] record.dividendYield,
   Part.optional [52, 54, 56] record.roundingDirection,
   Part.optional [50, 52, 49, 49, 48] record.aliasName,
   Part.optional [50, 52, 49, 49, 51] record.corporateActionCode,
   Part.optional [50, 52, 49, 49, 52] record.corporateActionCodeType,
   Part.optional [50, 52, 49, 49, 53] record.aSXSecurityType,
   Part.optional [50, 52, 49, 49, 54] record.aSXInstrumentClass,
   Part.optional [50, 52, 49, 49, 55] record.linkedCommodity,
   Part.optional [50, 52, 49, 49, 56] record.upperLevelInstrument,
   Part.optional [50, 52, 49, 49, 57] record.upperLevelInstrumentCode,
   Part.optional [50, 52, 49, 50, 48] record.accruedInterestRounding,
   Part.optional [50, 52, 49, 50, 49] record.cleanPriceRounding,
   Part.optional [50, 52, 49, 50, 50] record.yieldConvention,
   Part.optional [50, 52, 49, 50, 51] record.refSettlementDate,
   Part.optional [50, 52, 49, 50, 52] record.iTRminVal,
   Part.optional [50, 52, 49, 50, 53] record.extInfoInstrClass,
   Part.optional [50, 52, 49, 50, 54] record.foreignOwnFlag,
   Part.optional [50, 52, 49, 50, 55] record.practiseSec]

def NoRelatedSymUpdate.tags : List (List (List UInt8)) :=
  [[[49, 51, 50, 52]], [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[52, 54, 49]], [[53, 52, 49]], [[57, 54, 53]], [[50, 48, 50]], [[50, 53, 55, 55]], [[50, 51, 49]], [[49, 49, 57, 51]], [[49, 49, 57, 52]], [[50, 48, 49]], [[49, 48, 55]], [[49, 48, 54]], [56, 54, 52] :: NoEvents.members, [49, 50, 48, 53] :: NoTickRules.members, [[53, 54, 49]], [[49, 53]], [55, 49, 49] :: NoUnderlyings.members, [53, 53, 53] :: NoLegs.members, [56, 55, 48] :: NoInstrAttrib.members, [[50, 50, 56]], [[49, 57, 52, 56]], [[50, 50, 51]], [[50, 50, 53]], [[50, 50, 52]], [[50, 51, 48]], [[54, 51]], [[50, 53, 54, 55]], [[56, 55, 51]], [[49, 57, 53, 48]], [[49, 51, 56, 48]], [[52, 54, 56]], [[50, 52, 49, 49, 48]], [[50, 52, 49, 49, 51]], [[50, 52, 49, 49, 52]], [[50, 52, 49, 49, 53]], [[50, 52, 49, 49, 54]], [[50, 52, 49, 49, 55]], [[50, 52, 49, 49, 56]], [[50, 52, 49, 49, 57]], [[50, 52, 49, 50, 48]], [[50, 52, 49, 50, 49]], [[50, 52, 49, 50, 50]], [[50, 52, 49, 50, 51]], [[50, 52, 49, 50, 52]], [[50, 52, 49, 50, 53]], [[50, 52, 49, 50, 54]], [[50, 52, 49, 50, 55]]]

theorem NoRelatedSymUpdate.shape (record : NoRelatedSymUpdate) : record.parts.map Part.tags = NoRelatedSymUpdate.tags := rfl

def NoRelatedSymUpdate.decode (tokens : List Token) : Option NoRelatedSymUpdate := do
  let listUpdateAction ← readRequired [49, 51, 50, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let cFICode ← readOptional [52, 54, 49] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let securityStatus ← readOptional [57, 54, 53] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let strikePricePrecision ← readOptional [50, 53, 55, 55] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let settlMethod ← readOptional [49, 49, 57, 51] tokens
  let exerciseStyle ← readOptional [49, 49, 57, 52] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let issuer ← readOptional [49, 48, 54] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let noTickRules ← readGroup [49, 50, 48, 53] [49, 50, 48, 54] NoTickRules.members NoTickRules.decode tokens
  let roundLot ← readOptional [53, 54, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let noUnderlyings ← readGroup [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let noInstrAttrib ← readGroup [56, 55, 48] [56, 55, 49] NoInstrAttrib.members NoInstrAttrib.decode tokens
  let factor ← readOptional [50, 50, 56] tokens
  let couponFrequencyPeriod ← readOptional [49, 57, 52, 56] tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let couponPaymentDate ← readOptional [50, 50, 52] tokens
  let exDate ← readOptional [50, 51, 48] tokens
  let settlType ← readOptional [54, 51] tokens
  let instrumentPricePrecision ← readOptional [50, 53, 54, 55] tokens
  let datedDate ← readOptional [56, 55, 51] tokens
  let couponDayCount ← readOptional [49, 57, 53, 48] tokens
  let dividendYield ← readOptional [49, 51, 56, 48] tokens
  let roundingDirection ← readOptional [52, 54, 56] tokens
  let aliasName ← readOptional [50, 52, 49, 49, 48] tokens
  let corporateActionCode ← readOptional [50, 52, 49, 49, 51] tokens
  let corporateActionCodeType ← readOptional [50, 52, 49, 49, 52] tokens
  let aSXSecurityType ← readOptional [50, 52, 49, 49, 53] tokens
  let aSXInstrumentClass ← readOptional [50, 52, 49, 49, 54] tokens
  let linkedCommodity ← readOptional [50, 52, 49, 49, 55] tokens
  let upperLevelInstrument ← readOptional [50, 52, 49, 49, 56] tokens
  let upperLevelInstrumentCode ← readOptional [50, 52, 49, 49, 57] tokens
  let accruedInterestRounding ← readOptional [50, 52, 49, 50, 48] tokens
  let cleanPriceRounding ← readOptional [50, 52, 49, 50, 49] tokens
  let yieldConvention ← readOptional [50, 52, 49, 50, 50] tokens
  let refSettlementDate ← readOptional [50, 52, 49, 50, 51] tokens
  let iTRminVal ← readOptional [50, 52, 49, 50, 52] tokens
  let extInfoInstrClass ← readOptional [50, 52, 49, 50, 53] tokens
  let foreignOwnFlag ← readOptional [50, 52, 49, 50, 54] tokens
  let practiseSec ← readOptional [50, 52, 49, 50, 55] tokens
  pure { listUpdateAction, symbol, securityID, securityIDSource, noSecurityAltID, cFICode, maturityDate, securityStatus, strikePrice, strikePricePrecision, contractMultiplier, settlMethod, exerciseStyle, putOrCall, securityDesc, issuer, noEvents, noTickRules, roundLot, currency, noUnderlyings, noLegs, noInstrAttrib, factor, couponFrequencyPeriod, couponRate, issueDate, couponPaymentDate, exDate, settlType, instrumentPricePrecision, datedDate, couponDayCount, dividendYield, roundingDirection, aliasName, corporateActionCode, corporateActionCodeType, aSXSecurityType, aSXInstrumentClass, linkedCommodity, upperLevelInstrument, upperLevelInstrumentCode, accruedInterestRounding, cleanPriceRounding, yieldConvention, refSettlementDate, iTRminVal, extInfoInstrClass, foreignOwnFlag, practiseSec }

theorem NoRelatedSymUpdate.decode_agrees (record : NoRelatedSymUpdate) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSymUpdate.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSymUpdate.decode tokens = some record := by
  have distinct : NoRelatedSymUpdate.tags.flatten.Nodup := by decide +kernel
  have listUpdateAction := readRequired_part [49, 51, 50, 52] record.listUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cFICode := readOptional_part [52, 54, 49] record.cFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityStatus := readOptional_part [57, 54, 53] record.securityStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have strikePricePrecision := readOptional_part [50, 53, 55, 55] record.strikePricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have settlMethod := readOptional_part [49, 49, 57, 51] record.settlMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have exerciseStyle := readOptional_part [49, 49, 57, 52] record.exerciseStyle tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have issuer := readOptional_part [49, 48, 54] record.issuer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noTickRules := readGroup_part [49, 50, 48, 53] [49, 50, 48, 54] NoTickRules.members NoTickRules.encode NoTickRules.within NoTickRules.decode NoTickRules.decode_encode NoTickRules.led record.noTickRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have roundLot := readOptional_part [53, 54, 49] record.roundLot tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noUnderlyings := readGroup_part [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within NoUnderlyings.decode NoUnderlyings.decode_encode NoUnderlyings.led record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noInstrAttrib := readGroup_part [56, 55, 48] [56, 55, 49] NoInstrAttrib.members NoInstrAttrib.encode NoInstrAttrib.within NoInstrAttrib.decode NoInstrAttrib.decode_encode NoInstrAttrib.led record.noInstrAttrib tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have factor := readOptional_part [50, 50, 56] record.factor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have couponFrequencyPeriod := readOptional_part [49, 57, 52, 56] record.couponFrequencyPeriod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have couponPaymentDate := readOptional_part [50, 50, 52] record.couponPaymentDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have exDate := readOptional_part [50, 51, 48] record.exDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have instrumentPricePrecision := readOptional_part [50, 53, 54, 55] record.instrumentPricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have datedDate := readOptional_part [56, 55, 51] record.datedDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have couponDayCount := readOptional_part [49, 57, 53, 48] record.couponDayCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have dividendYield := readOptional_part [49, 51, 56, 48] record.dividendYield tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have roundingDirection := readOptional_part [52, 54, 56] record.roundingDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have aliasName := readOptional_part [50, 52, 49, 49, 48] record.aliasName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have corporateActionCode := readOptional_part [50, 52, 49, 49, 51] record.corporateActionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have corporateActionCodeType := readOptional_part [50, 52, 49, 49, 52] record.corporateActionCodeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have aSXSecurityType := readOptional_part [50, 52, 49, 49, 53] record.aSXSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have aSXInstrumentClass := readOptional_part [50, 52, 49, 49, 54] record.aSXInstrumentClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have linkedCommodity := readOptional_part [50, 52, 49, 49, 55] record.linkedCommodity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have upperLevelInstrument := readOptional_part [50, 52, 49, 49, 56] record.upperLevelInstrument tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have upperLevelInstrumentCode := readOptional_part [50, 52, 49, 49, 57] record.upperLevelInstrumentCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have accruedInterestRounding := readOptional_part [50, 52, 49, 50, 48] record.accruedInterestRounding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have cleanPriceRounding := readOptional_part [50, 52, 49, 50, 49] record.cleanPriceRounding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have yieldConvention := readOptional_part [50, 52, 49, 50, 50] record.yieldConvention tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refSettlementDate := readOptional_part [50, 52, 49, 50, 51] record.refSettlementDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have iTRminVal := readOptional_part [50, 52, 49, 50, 52] record.iTRminVal tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have extInfoInstrClass := readOptional_part [50, 52, 49, 50, 53] record.extInfoInstrClass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have foreignOwnFlag := readOptional_part [50, 52, 49, 50, 54] record.foreignOwnFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have practiseSec := readOptional_part [50, 52, 49, 50, 55] record.practiseSec tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  simp only [NoRelatedSymUpdate.decode, listUpdateAction, symbol, securityID, securityIDSource, noSecurityAltID, cFICode, maturityDate, securityStatus, strikePrice, strikePricePrecision, contractMultiplier, settlMethod, exerciseStyle, putOrCall, securityDesc, issuer, noEvents, noTickRules, roundLot, currency, noUnderlyings, noLegs, noInstrAttrib, factor, couponFrequencyPeriod, couponRate, issueDate, couponPaymentDate, exDate, settlType, instrumentPricePrecision, datedDate, couponDayCount, dividendYield, roundingDirection, aliasName, corporateActionCode, corporateActionCodeType, aSXSecurityType, aSXInstrumentClass, linkedCommodity, upperLevelInstrument, upperLevelInstrumentCode, accruedInterestRounding, cleanPriceRounding, yieldConvention, refSettlementDate, iTRminVal, extInfoInstrClass, foreignOwnFlag, practiseSec, some_bind] <;> rfl

def NoRelatedSymUpdate.members : List (List UInt8) := NoRelatedSymUpdate.tags.flatten

def NoRelatedSymUpdate.encode (entry : NoRelatedSymUpdate) : List Token := encodeParts entry.parts

theorem NoRelatedSymUpdate.decode_encode (entry : NoRelatedSymUpdate) : NoRelatedSymUpdate.decode entry.encode = some entry :=
  NoRelatedSymUpdate.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSymUpdate.within (entry : NoRelatedSymUpdate) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSymUpdate.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSymUpdate.shape] at this

theorem NoRelatedSymUpdate.led (entry : NoRelatedSymUpdate) : Lead [49, 51, 50, 52] entry.encode :=
  lead_parts [49, 51, 50, 52] entry.listUpdateAction _ NoRelatedSymUpdate.tags.tail rfl (by decide +kernel)

structure SecurityListUpdateReport where
  securityReqID : Option (Terminated 1)  -- tag 320
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300
  noRelatedSymUpdate : List NoRelatedSymUpdate  -- tag 146

def SecurityListUpdateReport.parts (record : SecurityListUpdateReport) : List Part :=
  [Part.optional [51, 50, 48] record.securityReqID,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID,
   Part.group [49, 52, 54] NoRelatedSymUpdate.members NoRelatedSymUpdate.encode NoRelatedSymUpdate.within record.noRelatedSymUpdate]

def SecurityListUpdateReport.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[49, 51, 48, 49]], [[49, 51, 48, 48]], [49, 52, 54] :: NoRelatedSymUpdate.members]

theorem SecurityListUpdateReport.shape (record : SecurityListUpdateReport) : record.parts.map Part.tags = SecurityListUpdateReport.tags := rfl

def SecurityListUpdateReport.decode (tokens : List Token) : Option SecurityListUpdateReport := do
  let securityReqID ← readOptional [51, 50, 48] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  let noRelatedSymUpdate ← readGroup [49, 52, 54] [49, 51, 50, 52] NoRelatedSymUpdate.members NoRelatedSymUpdate.decode tokens
  pure { securityReqID, marketID, marketSegmentID, noRelatedSymUpdate }

theorem SecurityListUpdateReport.decode_agrees (record : SecurityListUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityListUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityListUpdateReport.decode tokens = some record := by
  have distinct : SecurityListUpdateReport.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readOptional_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noRelatedSymUpdate := readGroup_part [49, 52, 54] [49, 51, 50, 52] NoRelatedSymUpdate.members NoRelatedSymUpdate.encode NoRelatedSymUpdate.within NoRelatedSymUpdate.decode NoRelatedSymUpdate.decode_encode NoRelatedSymUpdate.led record.noRelatedSymUpdate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityListUpdateReport.decode, securityReqID, marketID, marketSegmentID, noRelatedSymUpdate, some_bind] <;> rfl

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
  orderID : Terminated 1  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  execID : Terminated 1  -- tag 17
  noPartyIDs : List NoPartyIDs  -- tag 453
  trdMatchID : Option (Terminated 1)  -- tag 880
  execType : Terminated 1  -- tag 150
  ordStatus : Terminated 1  -- tag 39
  rejectText : Option (Terminated 1)  -- tag 1328
  execRestatementReason : Option (Terminated 1)  -- tag 378
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  symbol : Option (Terminated 1)  -- tag 55
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  pegPriceType : Option (Terminated 1)  -- tag 1094
  pegMoveType : Option (Terminated 1)  -- tag 835
  pegScope : Option (Terminated 1)  -- tag 840
  timeInForce : Option (Terminated 1)  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  orderCapacity : Option (Terminated 1)  -- tag 528
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  text : Option (Terminated 1)  -- tag 58
  directedWholesale : Option (Terminated 1)  -- tag 20013
  supplementaryInfo : Option (Terminated 1)  -- tag 24100
  customerInfo : Option (Terminated 1)  -- tag 24101
  optOutOfClearing : Option (Terminated 1)  -- tag 24107
  dealSource : Option (Terminated 1)  -- tag 24108
  changeReason : Option (Terminated 1)  -- tag 24109
  aliasName : Option (Terminated 1)  -- tag 24110
  tradeCondition : Option (Terminated 1)  -- tag 24112

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 49] record.clOrdID,
   Part.required [49, 55] record.execID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.required [49, 53, 48] record.execType,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 51, 50, 56] record.rejectText,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [56, 51, 53] record.pegMoveType,
   Part.optional [56, 52, 48] record.pegScope,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 48, 49, 51] record.directedWholesale,
   Part.optional [50, 52, 49, 48, 48] record.supplementaryInfo,
   Part.optional [50, 52, 49, 48, 49] record.customerInfo,
   Part.optional [50, 52, 49, 48, 55] record.optOutOfClearing,
   Part.optional [50, 52, 49, 48, 56] record.dealSource,
   Part.optional [50, 52, 49, 48, 57] record.changeReason,
   Part.optional [50, 52, 49, 49, 48] record.aliasName,
   Part.optional [50, 52, 49, 49, 50] record.tradeCondition]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[49, 55]], [52, 53, 51] :: NoPartyIDs.members, [[56, 56, 48]], [[49, 53, 48]], [[51, 57]], [[49, 51, 50, 56]], [[51, 55, 56]], [[52, 56]], [[50, 50]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 48, 57, 52]], [[56, 51, 53]], [[56, 52, 48]], [[53, 57]], [[52, 51, 50]], [[49, 56]], [[53, 50, 56]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[55, 53]], [[54, 48]], [[53, 56]], [[50, 48, 48, 49, 51]], [[50, 52, 49, 48, 48]], [[50, 52, 49, 48, 49]], [[50, 52, 49, 48, 55]], [[50, 52, 49, 48, 56]], [[50, 52, 49, 48, 57]], [[50, 52, 49, 49, 48]], [[50, 52, 49, 49, 50]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let rejectText ← readOptional [49, 51, 50, 56] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let symbol ← readOptional [53, 53] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let pegMoveType ← readOptional [56, 51, 53] tokens
  let pegScope ← readOptional [56, 52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let text ← readOptional [53, 56] tokens
  let directedWholesale ← readOptional [50, 48, 48, 49, 51] tokens
  let supplementaryInfo ← readOptional [50, 52, 49, 48, 48] tokens
  let customerInfo ← readOptional [50, 52, 49, 48, 49] tokens
  let optOutOfClearing ← readOptional [50, 52, 49, 48, 55] tokens
  let dealSource ← readOptional [50, 52, 49, 48, 56] tokens
  let changeReason ← readOptional [50, 52, 49, 48, 57] tokens
  let aliasName ← readOptional [50, 52, 49, 49, 48] tokens
  let tradeCondition ← readOptional [50, 52, 49, 49, 50] tokens
  pure { orderID, clOrdID, execID, noPartyIDs, trdMatchID, execType, ordStatus, rejectText, execRestatementReason, securityID, securityIDSource, symbol, side, orderQty, ordType, price, pegPriceType, pegMoveType, pegScope, timeInForce, expireDate, execInst, orderCapacity, lastQty, lastPx, leavesQty, cumQty, tradeDate, transactTime, text, directedWholesale, supplementaryInfo, customerInfo, optOutOfClearing, dealSource, changeReason, aliasName, tradeCondition }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have rejectText := readOptional_part [49, 51, 50, 56] record.rejectText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have pegMoveType := readOptional_part [56, 51, 53] record.pegMoveType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have pegScope := readOptional_part [56, 52, 48] record.pegScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have directedWholesale := readOptional_part [50, 48, 48, 49, 51] record.directedWholesale tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have supplementaryInfo := readOptional_part [50, 52, 49, 48, 48] record.supplementaryInfo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have customerInfo := readOptional_part [50, 52, 49, 48, 49] record.customerInfo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have optOutOfClearing := readOptional_part [50, 52, 49, 48, 55] record.optOutOfClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have dealSource := readOptional_part [50, 52, 49, 48, 56] record.dealSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have changeReason := readOptional_part [50, 52, 49, 48, 57] record.changeReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have aliasName := readOptional_part [50, 52, 49, 49, 48] record.aliasName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have tradeCondition := readOptional_part [50, 52, 49, 49, 50] record.tradeCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, execID, noPartyIDs, trdMatchID, execType, ordStatus, rejectText, execRestatementReason, securityID, securityIDSource, symbol, side, orderQty, ordType, price, pegPriceType, pegMoveType, pegScope, timeInForce, expireDate, execInst, orderCapacity, lastQty, lastPx, leavesQty, cumQty, tradeDate, transactTime, text, directedWholesale, supplementaryInfo, customerInfo, optOutOfClearing, dealSource, changeReason, aliasName, tradeCondition, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | marketDefinition (header : Header) (r0 : MarketDefinition)
  | tradingSessionList (header : Header) (r0 : TradingSessionList)
  | securityList (header : Header) (r0 : SecurityList)
  | securityListUpdateReport (header : Header) (r0 : SecurityListUpdateReport)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | executionReport (header : Header) (r0 : ExecutionReport)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDefinition header r0 => ⟨[51, 53], ⟨[66, 85], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionList header r0 => ⟨[51, 53], ⟨[66, 74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityList header r0 => ⟨[51, 53], ⟨[121], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityListUpdateReport header r0 => ⟨[51, 53], ⟨[66, 75], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value.val = [66, 85] then
        if known (Header.tags ++ MarketDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDefinition.decode rest
          pure (.marketDefinition header r0)
        else none
      else if token.value.val = [66, 74] then
        if known (Header.tags ++ TradingSessionList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionList.decode rest
          pure (.tradingSessionList header r0)
        else none
      else if token.value.val = [121] then
        if known (Header.tags ++ SecurityList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityList.decode rest
          pure (.securityList header r0)
        else none
      else if token.value.val = [66, 75] then
        if known (Header.tags ++ SecurityListUpdateReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityListUpdateReport.decode rest
          pure (.securityListUpdateReport header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
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

theorem Message.decode_marketDefinition (header : Header) (r0 : MarketDefinition) :
    Message.decode (Message.tokens (.marketDefinition header r0)) = some (.marketDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradingSessionList (header : Header) (r0 : TradingSessionList) :
    Message.decode (Message.tokens (.tradingSessionList header r0)) = some (.tradingSessionList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionList.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityList (header : Header) (r0 : SecurityList) :
    Message.decode (Message.tokens (.securityList header r0)) = some (.securityList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityListUpdateReport (header : Header) (r0 : SecurityListUpdateReport) :
    Message.decode (Message.tokens (.securityListUpdateReport header r0)) = some (.securityListUpdateReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListUpdateReport.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityListUpdateReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListUpdateReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityListUpdateReport.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDefinition header r0 => exact Message.decode_marketDefinition header r0
  | tradingSessionList header r0 => exact Message.decode_tradingSessionList header r0
  | securityList header r0 => exact Message.decode_securityList header r0
  | securityListUpdateReport header r0 => exact Message.decode_securityListUpdateReport header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0

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

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_marketDefinition (header : Header) (r0 : MarketDefinition) :
    Message.decodeBytes (Message.encode (.marketDefinition header r0)) = some (.marketDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 85], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDefinition header r0

theorem Message.decodeBytes_tradingSessionList (header : Header) (r0 : TradingSessionList) :
    Message.decodeBytes (Message.encode (.tradingSessionList header r0)) = some (.tradingSessionList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradingSessionList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionList header r0

theorem Message.decodeBytes_securityList (header : Header) (r0 : SecurityList) :
    Message.decodeBytes (Message.encode (.securityList header r0)) = some (.securityList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[121], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityList header r0

theorem Message.decodeBytes_securityListUpdateReport (header : Header) (r0 : SecurityListUpdateReport) :
    Message.decodeBytes (Message.encode (.securityListUpdateReport header r0)) = some (.securityListUpdateReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 75], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityListUpdateReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityListUpdateReport header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDefinition header r0 => exact Message.decodeBytes_marketDefinition header r0
  | tradingSessionList header r0 => exact Message.decodeBytes_tradingSessionList header r0
  | securityList header r0 => exact Message.decodeBytes_securityList header r0
  | securityListUpdateReport header r0 => exact Message.decodeBytes_securityListUpdateReport header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AsxAsxsecuritiesDropcopyFixV11Exchange
