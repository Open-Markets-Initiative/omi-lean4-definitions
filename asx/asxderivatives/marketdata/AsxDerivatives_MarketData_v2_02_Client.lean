import Wire

/-!
# Australian Securities Exchange Market Data v2.02, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxderivativesMarketdataFixV202Client

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

structure NoRelatedSymMarketData where
  symbol : Terminated 1  -- tag 55

def NoRelatedSymMarketData.parts (record : NoRelatedSymMarketData) : List Part :=
  [Part.required [53, 53] record.symbol]

def NoRelatedSymMarketData.tags : List (List (List UInt8)) :=
  [[[53, 53]]]

theorem NoRelatedSymMarketData.shape (record : NoRelatedSymMarketData) : record.parts.map Part.tags = NoRelatedSymMarketData.tags := rfl

def NoRelatedSymMarketData.decode (tokens : List Token) : Option NoRelatedSymMarketData := do
  let symbol ← readRequired [53, 53] tokens
  pure { symbol }

theorem NoRelatedSymMarketData.decode_agrees (record : NoRelatedSymMarketData) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSymMarketData.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSymMarketData.decode tokens = some record := by
  have distinct : NoRelatedSymMarketData.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoRelatedSymMarketData.decode, symbol, some_bind] <;> rfl

def NoRelatedSymMarketData.members : List (List UInt8) := NoRelatedSymMarketData.tags.flatten

def NoRelatedSymMarketData.encode (entry : NoRelatedSymMarketData) : List Token := encodeParts entry.parts

theorem NoRelatedSymMarketData.decode_encode (entry : NoRelatedSymMarketData) : NoRelatedSymMarketData.decode entry.encode = some entry :=
  NoRelatedSymMarketData.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSymMarketData.within (entry : NoRelatedSymMarketData) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSymMarketData.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSymMarketData.shape] at this

theorem NoRelatedSymMarketData.led (entry : NoRelatedSymMarketData) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSymMarketData.tags.tail rfl (by decide +kernel)

structure NoMarketSegments where
  marketID : Terminated 1  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300

def NoMarketSegments.parts (record : NoMarketSegments) : List Part :=
  [Part.required [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID]

def NoMarketSegments.tags : List (List (List UInt8)) :=
  [[[49, 51, 48, 49]], [[49, 51, 48, 48]]]

theorem NoMarketSegments.shape (record : NoMarketSegments) : record.parts.map Part.tags = NoMarketSegments.tags := rfl

def NoMarketSegments.decode (tokens : List Token) : Option NoMarketSegments := do
  let marketID ← readRequired [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  pure { marketID, marketSegmentID }

theorem NoMarketSegments.decode_agrees (record : NoMarketSegments) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMarketSegments.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMarketSegments.decode tokens = some record := by
  have distinct : NoMarketSegments.tags.flatten.Nodup := by decide +kernel
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoMarketSegments.decode, marketID, marketSegmentID, some_bind] <;> rfl

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

structure NoTradeSeqNoSeries where
  tradeSeqNoSeries : Terminated 1  -- tag 7555
  tradeSeqNo : Option (Terminated 1)  -- tag 7554

def NoTradeSeqNoSeries.parts (record : NoTradeSeqNoSeries) : List Part :=
  [Part.required [55, 53, 53, 53] record.tradeSeqNoSeries,
   Part.optional [55, 53, 53, 52] record.tradeSeqNo]

def NoTradeSeqNoSeries.tags : List (List (List UInt8)) :=
  [[[55, 53, 53, 53]], [[55, 53, 53, 52]]]

theorem NoTradeSeqNoSeries.shape (record : NoTradeSeqNoSeries) : record.parts.map Part.tags = NoTradeSeqNoSeries.tags := rfl

def NoTradeSeqNoSeries.decode (tokens : List Token) : Option NoTradeSeqNoSeries := do
  let tradeSeqNoSeries ← readRequired [55, 53, 53, 53] tokens
  let tradeSeqNo ← readOptional [55, 53, 53, 52] tokens
  pure { tradeSeqNoSeries, tradeSeqNo }

theorem NoTradeSeqNoSeries.decode_agrees (record : NoTradeSeqNoSeries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradeSeqNoSeries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradeSeqNoSeries.decode tokens = some record := by
  have distinct : NoTradeSeqNoSeries.tags.flatten.Nodup := by decide +kernel
  have tradeSeqNoSeries := readRequired_part [55, 53, 53, 53] record.tradeSeqNoSeries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeSeqNo := readOptional_part [55, 53, 53, 52] record.tradeSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTradeSeqNoSeries.decode, tradeSeqNoSeries, tradeSeqNo, some_bind] <;> rfl

def NoTradeSeqNoSeries.members : List (List UInt8) := NoTradeSeqNoSeries.tags.flatten

def NoTradeSeqNoSeries.encode (entry : NoTradeSeqNoSeries) : List Token := encodeParts entry.parts

theorem NoTradeSeqNoSeries.decode_encode (entry : NoTradeSeqNoSeries) : NoTradeSeqNoSeries.decode entry.encode = some entry :=
  NoTradeSeqNoSeries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradeSeqNoSeries.within (entry : NoTradeSeqNoSeries) : ∀ token ∈ entry.encode, token.tag ∈ NoTradeSeqNoSeries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradeSeqNoSeries.shape] at this

theorem NoTradeSeqNoSeries.led (entry : NoTradeSeqNoSeries) : Lead [55, 53, 53, 53] entry.encode :=
  lead_parts [55, 53, 53, 53] entry.tradeSeqNoSeries _ NoTradeSeqNoSeries.tags.tail rfl (by decide +kernel)

structure MarketDataRequest where
  mDReqID : Terminated 1  -- tag 262
  subscriptionRequestType : Terminated 1  -- tag 263
  marketDepth : Terminated 1  -- tag 264
  mDUpdateType : Option (Terminated 1)  -- tag 265
  aggregatedBook : Option (Terminated 1)  -- tag 266
  noMDEntryTypes : List NoMDEntryTypes  -- tag 267
  noRelatedSymMarketData : List NoRelatedSymMarketData  -- tag 146
  noMarketSegments : List NoMarketSegments  -- tag 1310
  noTradeSeqNoSeries : List NoTradeSeqNoSeries  -- tag 7565

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.required [50, 54, 52] record.marketDepth,
   Part.optional [50, 54, 53] record.mDUpdateType,
   Part.optional [50, 54, 54] record.aggregatedBook,
   Part.group [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within record.noMDEntryTypes,
   Part.group [49, 52, 54] NoRelatedSymMarketData.members NoRelatedSymMarketData.encode NoRelatedSymMarketData.within record.noRelatedSymMarketData,
   Part.group [49, 51, 49, 48] NoMarketSegments.members NoMarketSegments.encode NoMarketSegments.within record.noMarketSegments,
   Part.group [55, 53, 54, 53] NoTradeSeqNoSeries.members NoTradeSeqNoSeries.encode NoTradeSeqNoSeries.within record.noTradeSeqNoSeries]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [[50, 54, 52]], [[50, 54, 53]], [[50, 54, 54]], [50, 54, 55] :: NoMDEntryTypes.members, [49, 52, 54] :: NoRelatedSymMarketData.members, [49, 51, 49, 48] :: NoMarketSegments.members, [55, 53, 54, 53] :: NoTradeSeqNoSeries.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let marketDepth ← readRequired [50, 54, 52] tokens
  let mDUpdateType ← readOptional [50, 54, 53] tokens
  let aggregatedBook ← readOptional [50, 54, 54] tokens
  let noMDEntryTypes ← readGroup [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.decode tokens
  let noRelatedSymMarketData ← readGroup [49, 52, 54] [53, 53] NoRelatedSymMarketData.members NoRelatedSymMarketData.decode tokens
  let noMarketSegments ← readGroup [49, 51, 49, 48] [49, 51, 48, 49] NoMarketSegments.members NoMarketSegments.decode tokens
  let noTradeSeqNoSeries ← readGroup [55, 53, 54, 53] [55, 53, 53, 53] NoTradeSeqNoSeries.members NoTradeSeqNoSeries.decode tokens
  pure { mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, aggregatedBook, noMDEntryTypes, noRelatedSymMarketData, noMarketSegments, noTradeSeqNoSeries }

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
  have noMDEntryTypes := readGroup_part [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within NoMDEntryTypes.decode NoMDEntryTypes.decode_encode NoMDEntryTypes.led record.noMDEntryTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRelatedSymMarketData := readGroup_part [49, 52, 54] [53, 53] NoRelatedSymMarketData.members NoRelatedSymMarketData.encode NoRelatedSymMarketData.within NoRelatedSymMarketData.decode NoRelatedSymMarketData.decode_encode NoRelatedSymMarketData.led record.noRelatedSymMarketData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noMarketSegments := readGroup_part [49, 51, 49, 48] [49, 51, 48, 49] NoMarketSegments.members NoMarketSegments.encode NoMarketSegments.within NoMarketSegments.decode NoMarketSegments.decode_encode NoMarketSegments.led record.noMarketSegments tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noTradeSeqNoSeries := readGroup_part [55, 53, 54, 53] [55, 53, 53, 53] NoTradeSeqNoSeries.members NoTradeSeqNoSeries.encode NoTradeSeqNoSeries.within NoTradeSeqNoSeries.decode NoTradeSeqNoSeries.decode_encode NoTradeSeqNoSeries.led record.noTradeSeqNoSeries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, aggregatedBook, noMDEntryTypes, noRelatedSymMarketData, noMarketSegments, noTradeSeqNoSeries, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
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

structure NoRelatedSymRfq where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def NoRelatedSymRfq.parts (record : NoRelatedSymRfq) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def NoRelatedSymRfq.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]]]

theorem NoRelatedSymRfq.shape (record : NoRelatedSymRfq) : record.parts.map Part.tags = NoRelatedSymRfq.tags := rfl

def NoRelatedSymRfq.decode (tokens : List Token) : Option NoRelatedSymRfq := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { symbol, securityID, securityIDSource }

theorem NoRelatedSymRfq.decode_agrees (record : NoRelatedSymRfq) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSymRfq.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSymRfq.decode tokens = some record := by
  have distinct : NoRelatedSymRfq.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRelatedSymRfq.decode, symbol, securityID, securityIDSource, some_bind] <;> rfl

def NoRelatedSymRfq.members : List (List UInt8) := NoRelatedSymRfq.tags.flatten

def NoRelatedSymRfq.encode (entry : NoRelatedSymRfq) : List Token := encodeParts entry.parts

theorem NoRelatedSymRfq.decode_encode (entry : NoRelatedSymRfq) : NoRelatedSymRfq.decode entry.encode = some entry :=
  NoRelatedSymRfq.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSymRfq.within (entry : NoRelatedSymRfq) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSymRfq.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSymRfq.shape] at this

theorem NoRelatedSymRfq.led (entry : NoRelatedSymRfq) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSymRfq.tags.tail rfl (by decide +kernel)

structure RFQRequest where
  rFQReqID : Terminated 1  -- tag 644
  noPartyIDs : List NoPartyIDs  -- tag 453
  noRelatedSymRfq : List NoRelatedSymRfq  -- tag 146

def RFQRequest.parts (record : RFQRequest) : List Part :=
  [Part.required [54, 52, 52] record.rFQReqID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 52, 54] NoRelatedSymRfq.members NoRelatedSymRfq.encode NoRelatedSymRfq.within record.noRelatedSymRfq]

def RFQRequest.tags : List (List (List UInt8)) :=
  [[[54, 52, 52]], [52, 53, 51] :: NoPartyIDs.members, [49, 52, 54] :: NoRelatedSymRfq.members]

theorem RFQRequest.shape (record : RFQRequest) : record.parts.map Part.tags = RFQRequest.tags := rfl

def RFQRequest.decode (tokens : List Token) : Option RFQRequest := do
  let rFQReqID ← readRequired [54, 52, 52] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noRelatedSymRfq ← readGroup [49, 52, 54] [53, 53] NoRelatedSymRfq.members NoRelatedSymRfq.decode tokens
  pure { rFQReqID, noPartyIDs, noRelatedSymRfq }

theorem RFQRequest.decode_agrees (record : RFQRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ RFQRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RFQRequest.decode tokens = some record := by
  have distinct : RFQRequest.tags.flatten.Nodup := by decide +kernel
  have rFQReqID := readRequired_part [54, 52, 52] record.rFQReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSymRfq := readGroup_part [49, 52, 54] [53, 53] NoRelatedSymRfq.members NoRelatedSymRfq.encode NoRelatedSymRfq.within NoRelatedSymRfq.decode NoRelatedSymRfq.decode_encode NoRelatedSymRfq.led record.noRelatedSymRfq tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [RFQRequest.decode, rFQReqID, noPartyIDs, noRelatedSymRfq, some_bind] <;> rfl

structure MarketDefinitionRequest where
  marketReqID : Terminated 1  -- tag 1393
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300

def MarketDefinitionRequest.parts (record : MarketDefinitionRequest) : List Part :=
  [Part.required [49, 51, 57, 51] record.marketReqID,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID]

def MarketDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 57, 51]], [[50, 54, 51]], [[49, 51, 48, 49]], [[49, 51, 48, 48]]]

theorem MarketDefinitionRequest.shape (record : MarketDefinitionRequest) : record.parts.map Part.tags = MarketDefinitionRequest.tags := rfl

def MarketDefinitionRequest.decode (tokens : List Token) : Option MarketDefinitionRequest := do
  let marketReqID ← readRequired [49, 51, 57, 51] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  pure { marketReqID, subscriptionRequestType, marketID, marketSegmentID }

theorem MarketDefinitionRequest.decode_agrees (record : MarketDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDefinitionRequest.decode tokens = some record := by
  have distinct : MarketDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have marketReqID := readRequired_part [49, 51, 57, 51] record.marketReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [MarketDefinitionRequest.decode, marketReqID, subscriptionRequestType, marketID, marketSegmentID, some_bind] <;> rfl

structure SecurityListRequest where
  securityReqID : Terminated 1  -- tag 320
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  securityListRequestType : Terminated 1  -- tag 559
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300

def SecurityListRequest.parts (record : SecurityListRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.required [53, 53, 57] record.securityListRequestType,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID]

def SecurityListRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[50, 54, 51]], [[53, 53, 57]], [[49, 51, 48, 49]], [[49, 51, 48, 48]]]

theorem SecurityListRequest.shape (record : SecurityListRequest) : record.parts.map Part.tags = SecurityListRequest.tags := rfl

def SecurityListRequest.decode (tokens : List Token) : Option SecurityListRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let securityListRequestType ← readRequired [53, 53, 57] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  pure { securityReqID, subscriptionRequestType, securityListRequestType, marketID, marketSegmentID }

theorem SecurityListRequest.decode_agrees (record : SecurityListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityListRequest.decode tokens = some record := by
  have distinct : SecurityListRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityListRequestType := readRequired_part [53, 53, 57] record.securityListRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [SecurityListRequest.decode, securityReqID, subscriptionRequestType, securityListRequestType, marketID, marketSegmentID, some_bind] <;> rfl

structure DerivativeSecurityListRequest where
  securityReqID : Terminated 1  -- tag 320
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  securityListRequestType : Option (Terminated 1)  -- tag 559
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300

def DerivativeSecurityListRequest.parts (record : DerivativeSecurityListRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [53, 53, 57] record.securityListRequestType,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID]

def DerivativeSecurityListRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[50, 54, 51]], [[53, 53, 57]], [[49, 51, 48, 49]], [[49, 51, 48, 48]]]

theorem DerivativeSecurityListRequest.shape (record : DerivativeSecurityListRequest) : record.parts.map Part.tags = DerivativeSecurityListRequest.tags := rfl

def DerivativeSecurityListRequest.decode (tokens : List Token) : Option DerivativeSecurityListRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let securityListRequestType ← readOptional [53, 53, 57] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  pure { securityReqID, subscriptionRequestType, securityListRequestType, marketID, marketSegmentID }

theorem DerivativeSecurityListRequest.decode_agrees (record : DerivativeSecurityListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ DerivativeSecurityListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    DerivativeSecurityListRequest.decode tokens = some record := by
  have distinct : DerivativeSecurityListRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityListRequestType := readOptional_part [53, 53, 57] record.securityListRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [DerivativeSecurityListRequest.decode, securityReqID, subscriptionRequestType, securityListRequestType, marketID, marketSegmentID, some_bind] <;> rfl

structure TradingSessionStatusRequest where
  tradSesReqID : Terminated 1  -- tag 335
  marketID : Option (Terminated 1)  -- tag 1301
  marketSegmentID : Option (Terminated 1)  -- tag 1300
  subscriptionRequestType : Option (Terminated 1)  -- tag 263

def TradingSessionStatusRequest.parts (record : TradingSessionStatusRequest) : List Part :=
  [Part.required [51, 51, 53] record.tradSesReqID,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 51, 48, 48] record.marketSegmentID,
   Part.optional [50, 54, 51] record.subscriptionRequestType]

def TradingSessionStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 51, 53]], [[49, 51, 48, 49]], [[49, 51, 48, 48]], [[50, 54, 51]]]

theorem TradingSessionStatusRequest.shape (record : TradingSessionStatusRequest) : record.parts.map Part.tags = TradingSessionStatusRequest.tags := rfl

def TradingSessionStatusRequest.decode (tokens : List Token) : Option TradingSessionStatusRequest := do
  let tradSesReqID ← readRequired [51, 51, 53] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  pure { tradSesReqID, marketID, marketSegmentID, subscriptionRequestType }

theorem TradingSessionStatusRequest.decode_agrees (record : TradingSessionStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionStatusRequest.decode tokens = some record := by
  have distinct : TradingSessionStatusRequest.tags.flatten.Nodup := by decide +kernel
  have tradSesReqID := readRequired_part [51, 51, 53] record.tradSesReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TradingSessionStatusRequest.decode, tradSesReqID, marketID, marketSegmentID, subscriptionRequestType, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)
  | rFQRequest (header : Header) (r0 : RFQRequest)
  | marketDefinitionRequest (header : Header) (r0 : MarketDefinitionRequest)
  | securityListRequest (header : Header) (r0 : SecurityListRequest)
  | derivativeSecurityListRequest (header : Header) (r0 : DerivativeSecurityListRequest)
  | tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], ⟨[86], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .rFQRequest header r0 => ⟨[51, 53], ⟨[65, 72], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDefinitionRequest header r0 => ⟨[51, 53], ⟨[66, 84], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityListRequest header r0 => ⟨[51, 53], ⟨[120], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .derivativeSecurityListRequest header r0 => ⟨[51, 53], ⟨[122], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionStatusRequest header r0 => ⟨[51, 53], ⟨[103], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [86] then
        if known (Header.tags ++ MarketDataRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequest.decode rest
          pure (.marketDataRequest header r0)
        else none
      else if token.value.val = [65, 72] then
        if known (Header.tags ++ RFQRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RFQRequest.decode rest
          pure (.rFQRequest header r0)
        else none
      else if token.value.val = [66, 84] then
        if known (Header.tags ++ MarketDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDefinitionRequest.decode rest
          pure (.marketDefinitionRequest header r0)
        else none
      else if token.value.val = [120] then
        if known (Header.tags ++ SecurityListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityListRequest.decode rest
          pure (.securityListRequest header r0)
        else none
      else if token.value.val = [122] then
        if known (Header.tags ++ DerivativeSecurityListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← DerivativeSecurityListRequest.decode rest
          pure (.derivativeSecurityListRequest header r0)
        else none
      else if token.value.val = [103] then
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

theorem Message.decode_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decode (Message.tokens (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_rFQRequest (header : Header) (r0 : RFQRequest) :
    Message.decode (Message.tokens (.rFQRequest header r0)) = some (.rFQRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RFQRequest.tags) rfl rfl (by decide +kernel))
  have c1 := RFQRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RFQRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RFQRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDefinitionRequest (header : Header) (r0 : MarketDefinitionRequest) :
    Message.decode (Message.tokens (.marketDefinitionRequest header r0)) = some (.marketDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decode (Message.tokens (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_derivativeSecurityListRequest (header : Header) (r0 : DerivativeSecurityListRequest) :
    Message.decode (Message.tokens (.derivativeSecurityListRequest header r0)) = some (.derivativeSecurityListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (DerivativeSecurityListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := DerivativeSecurityListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (DerivativeSecurityListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ DerivativeSecurityListRequest.tags) rfl
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
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0
  | rFQRequest header r0 => exact Message.decode_rFQRequest header r0
  | marketDefinitionRequest header r0 => exact Message.decode_marketDefinitionRequest header r0
  | securityListRequest header r0 => exact Message.decode_securityListRequest header r0
  | derivativeSecurityListRequest header r0 => exact Message.decode_derivativeSecurityListRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decode_tradingSessionStatusRequest header r0

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

theorem Message.decodeBytes_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decodeBytes (Message.encode (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[86], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequest header r0

theorem Message.decodeBytes_rFQRequest (header : Header) (r0 : RFQRequest) :
    Message.decodeBytes (Message.encode (.rFQRequest header r0)) = some (.rFQRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 72], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RFQRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_rFQRequest header r0

theorem Message.decodeBytes_marketDefinitionRequest (header : Header) (r0 : MarketDefinitionRequest) :
    Message.decodeBytes (Message.encode (.marketDefinitionRequest header r0)) = some (.marketDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 84], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDefinitionRequest header r0

theorem Message.decodeBytes_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decodeBytes (Message.encode (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[120], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityListRequest header r0

theorem Message.decodeBytes_derivativeSecurityListRequest (header : Header) (r0 : DerivativeSecurityListRequest) :
    Message.decodeBytes (Message.encode (.derivativeSecurityListRequest header r0)) = some (.derivativeSecurityListRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[122], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ DerivativeSecurityListRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_derivativeSecurityListRequest header r0

theorem Message.decodeBytes_tradingSessionStatusRequest (header : Header) (r0 : TradingSessionStatusRequest) :
    Message.decodeBytes (Message.encode (.tradingSessionStatusRequest header r0)) = some (.tradingSessionStatusRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[103], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradingSessionStatusRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
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
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0
  | rFQRequest header r0 => exact Message.decodeBytes_rFQRequest header r0
  | marketDefinitionRequest header r0 => exact Message.decodeBytes_marketDefinitionRequest header r0
  | securityListRequest header r0 => exact Message.decodeBytes_securityListRequest header r0
  | derivativeSecurityListRequest header r0 => exact Message.decodeBytes_derivativeSecurityListRequest header r0
  | tradingSessionStatusRequest header r0 => exact Message.decodeBytes_tradingSessionStatusRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AsxAsxderivativesMarketdataFixV202Client
