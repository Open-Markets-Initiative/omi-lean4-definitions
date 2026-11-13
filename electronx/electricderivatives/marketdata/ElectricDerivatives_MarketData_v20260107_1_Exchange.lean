import Wire

/-!
# ElectronX Markets Market Data v20260107.1, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.ElectronxElectricderivativesMarketdataFixV202601071Exchange

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID }

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
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Terminated 1  -- tag 141
  password : Option (Terminated 1)  -- tag 554
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [53, 53, 52] record.password,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 52]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readRequired [49, 52, 49] tokens
  let password ← readOptional [53, 53, 52] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, password, defaultApplVerID }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have resetSeqNumFlag := readRequired_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, password, defaultApplVerID, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
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
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, some_bind] <;> rfl

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refMsgType : Terminated 1  -- tag 372
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Terminated 1  -- tag 380

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [51, 56, 48] record.businessRejectReason]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 50]], [[51, 55, 57]], [[51, 56, 48]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  pure { refSeqNum, text, refMsgType, businessRejectRefID, businessRejectReason }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, text, refMsgType, businessRejectRefID, businessRejectReason, some_bind] <;> rfl

structure NoMDEntries where
  mDEntryType : Terminated 1  -- tag 269
  mDEntryPx : Terminated 1  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryDate : Terminated 1  -- tag 272
  mDEntryTime : Terminated 1  -- tag 273
  mDEntryID : Terminated 1  -- tag 278
  trdType : Option (Terminated 1)  -- tag 828
  mDQuoteType : Option (Terminated 1)  -- tag 1070
  tradingSessionID : Option (Terminated 1)  -- tag 336

def NoMDEntries.parts (record : NoMDEntries) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType,
   Part.required [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.required [50, 55, 50] record.mDEntryDate,
   Part.required [50, 55, 51] record.mDEntryTime,
   Part.required [50, 55, 56] record.mDEntryID,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [49, 48, 55, 48] record.mDQuoteType,
   Part.optional [51, 51, 54] record.tradingSessionID]

def NoMDEntries.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]], [[50, 55, 48]], [[50, 55, 49]], [[50, 55, 50]], [[50, 55, 51]], [[50, 55, 56]], [[56, 50, 56]], [[49, 48, 55, 48]], [[51, 51, 54]]]

theorem NoMDEntries.shape (record : NoMDEntries) : record.parts.map Part.tags = NoMDEntries.tags := rfl

def NoMDEntries.decode (tokens : List Token) : Option NoMDEntries := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  let mDEntryPx ← readRequired [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryDate ← readRequired [50, 55, 50] tokens
  let mDEntryTime ← readRequired [50, 55, 51] tokens
  let mDEntryID ← readRequired [50, 55, 56] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let mDQuoteType ← readOptional [49, 48, 55, 48] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  pure { mDEntryType, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, mDEntryID, trdType, mDQuoteType, tradingSessionID }

theorem NoMDEntries.decode_agrees (record : NoMDEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntries.decode tokens = some record := by
  have distinct : NoMDEntries.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryPx := readRequired_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDEntryDate := readRequired_part [50, 55, 50] record.mDEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have mDEntryTime := readRequired_part [50, 55, 51] record.mDEntryTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have mDEntryID := readRequired_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have mDQuoteType := readOptional_part [49, 48, 55, 48] record.mDQuoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoMDEntries.decode, mDEntryType, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, mDEntryID, trdType, mDQuoteType, tradingSessionID, some_bind] <;> rfl

def NoMDEntries.members : List (List UInt8) := NoMDEntries.tags.flatten

def NoMDEntries.encode (entry : NoMDEntries) : List Token := encodeParts entry.parts

theorem NoMDEntries.decode_encode (entry : NoMDEntries) : NoMDEntries.decode entry.encode = some entry :=
  NoMDEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntries.within (entry : NoMDEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntries.shape] at this

theorem NoMDEntries.led (entry : NoMDEntries) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMDEntries.tags.tail rfl (by decide +kernel)

structure MarketDataSnapshotFullRefresh where
  securityIDSource : Terminated 1  -- tag 22
  securityID : Terminated 1  -- tag 48
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  mDReqID : Terminated 1  -- tag 262
  noMDEntries : List NoMDEntries  -- tag 268
  securityGroup : Option (Terminated 1)  -- tag 1151

def MarketDataSnapshotFullRefresh.parts (record : MarketDataSnapshotFullRefresh) : List Part :=
  [Part.required [50, 50] record.securityIDSource,
   Part.required [52, 56] record.securityID,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 54, 50] record.mDReqID,
   Part.group [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within record.noMDEntries,
   Part.optional [49, 49, 53, 49] record.securityGroup]

def MarketDataSnapshotFullRefresh.tags : List (List (List UInt8)) :=
  [[[50, 50]], [[52, 56]], [[53, 53]], [[49, 54, 55]], [[50, 54, 50]], [50, 54, 56] :: NoMDEntries.members, [[49, 49, 53, 49]]]

theorem MarketDataSnapshotFullRefresh.shape (record : MarketDataSnapshotFullRefresh) : record.parts.map Part.tags = MarketDataSnapshotFullRefresh.tags := rfl

def MarketDataSnapshotFullRefresh.decode (tokens : List Token) : Option MarketDataSnapshotFullRefresh := do
  let securityIDSource ← readRequired [50, 50] tokens
  let securityID ← readRequired [52, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let mDReqID ← readRequired [50, 54, 50] tokens
  let noMDEntries ← readGroup [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.decode tokens
  let securityGroup ← readOptional [49, 49, 53, 49] tokens
  pure { securityIDSource, securityID, symbol, securityType, mDReqID, noMDEntries, securityGroup }

theorem MarketDataSnapshotFullRefresh.decode_agrees (record : MarketDataSnapshotFullRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataSnapshotFullRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataSnapshotFullRefresh.decode tokens = some record := by
  have distinct : MarketDataSnapshotFullRefresh.tags.flatten.Nodup := by decide +kernel
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noMDEntries := readGroup_part [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.encode NoMDEntries.within NoMDEntries.decode NoMDEntries.decode_encode NoMDEntries.led record.noMDEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityGroup := readOptional_part [49, 49, 53, 49] record.securityGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [MarketDataSnapshotFullRefresh.decode, securityIDSource, securityID, symbol, securityType, mDReqID, noMDEntries, securityGroup, some_bind] <;> rfl

structure NoMDEntriesIncremental where
  mDUpdateAction : Terminated 1  -- tag 279
  mDEntryType : Option (Terminated 1)  -- tag 269
  mDEntryID : Option (Terminated 1)  -- tag 278
  mDQuoteType : Option (Terminated 1)  -- tag 1070
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  securityType : Terminated 1  -- tag 167
  securityGroup : Option (Terminated 1)  -- tag 1151
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryDate : Option (Terminated 1)  -- tag 272
  mDEntryTime : Option (Terminated 1)  -- tag 273
  trdType : Option (Terminated 1)  -- tag 828
  tradeID : Option (Terminated 1)  -- tag 1003
  aggressorSide : Option (Terminated 1)  -- tag 2446
  tradingSessionID : Option (Terminated 1)  -- tag 336

def NoMDEntriesIncremental.parts (record : NoMDEntriesIncremental) : List Part :=
  [Part.required [50, 55, 57] record.mDUpdateAction,
   Part.optional [50, 54, 57] record.mDEntryType,
   Part.optional [50, 55, 56] record.mDEntryID,
   Part.optional [49, 48, 55, 48] record.mDQuoteType,
   Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [49, 49, 53, 49] record.securityGroup,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 55, 50] record.mDEntryDate,
   Part.optional [50, 55, 51] record.mDEntryTime,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [50, 52, 52, 54] record.aggressorSide,
   Part.optional [51, 51, 54] record.tradingSessionID]

def NoMDEntriesIncremental.tags : List (List (List UInt8)) :=
  [[[50, 55, 57]], [[50, 54, 57]], [[50, 55, 56]], [[49, 48, 55, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [[49, 54, 55]], [[49, 49, 53, 49]], [[50, 55, 48]], [[50, 55, 49]], [[50, 55, 50]], [[50, 55, 51]], [[56, 50, 56]], [[49, 48, 48, 51]], [[50, 52, 52, 54]], [[51, 51, 54]]]

theorem NoMDEntriesIncremental.shape (record : NoMDEntriesIncremental) : record.parts.map Part.tags = NoMDEntriesIncremental.tags := rfl

def NoMDEntriesIncremental.decode (tokens : List Token) : Option NoMDEntriesIncremental := do
  let mDUpdateAction ← readRequired [50, 55, 57] tokens
  let mDEntryType ← readOptional [50, 54, 57] tokens
  let mDEntryID ← readOptional [50, 55, 56] tokens
  let mDQuoteType ← readOptional [49, 48, 55, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securityGroup ← readOptional [49, 49, 53, 49] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryDate ← readOptional [50, 55, 50] tokens
  let mDEntryTime ← readOptional [50, 55, 51] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let aggressorSide ← readOptional [50, 52, 52, 54] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  pure { mDUpdateAction, mDEntryType, mDEntryID, mDQuoteType, symbol, securityID, securityIDSource, securityType, securityGroup, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, trdType, tradeID, aggressorSide, tradingSessionID }

theorem NoMDEntriesIncremental.decode_agrees (record : NoMDEntriesIncremental) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntriesIncremental.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntriesIncremental.decode tokens = some record := by
  have distinct : NoMDEntriesIncremental.tags.flatten.Nodup := by decide +kernel
  have mDUpdateAction := readRequired_part [50, 55, 57] record.mDUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryType := readOptional_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntryID := readOptional_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDQuoteType := readOptional_part [49, 48, 55, 48] record.mDQuoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityGroup := readOptional_part [49, 49, 53, 49] record.securityGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have mDEntryDate := readOptional_part [50, 55, 50] record.mDEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have mDEntryTime := readOptional_part [50, 55, 51] record.mDEntryTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have aggressorSide := readOptional_part [50, 52, 52, 54] record.aggressorSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [NoMDEntriesIncremental.decode, mDUpdateAction, mDEntryType, mDEntryID, mDQuoteType, symbol, securityID, securityIDSource, securityType, securityGroup, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, trdType, tradeID, aggressorSide, tradingSessionID, some_bind] <;> rfl

def NoMDEntriesIncremental.members : List (List UInt8) := NoMDEntriesIncremental.tags.flatten

def NoMDEntriesIncremental.encode (entry : NoMDEntriesIncremental) : List Token := encodeParts entry.parts

theorem NoMDEntriesIncremental.decode_encode (entry : NoMDEntriesIncremental) : NoMDEntriesIncremental.decode entry.encode = some entry :=
  NoMDEntriesIncremental.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntriesIncremental.within (entry : NoMDEntriesIncremental) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntriesIncremental.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntriesIncremental.shape] at this

theorem NoMDEntriesIncremental.led (entry : NoMDEntriesIncremental) : Lead [50, 55, 57] entry.encode :=
  lead_parts [50, 55, 57] entry.mDUpdateAction _ NoMDEntriesIncremental.tags.tail rfl (by decide +kernel)

structure MarketDataIncrementalRefresh where
  mDReqID : Terminated 1  -- tag 262
  noMDEntriesIncremental : List NoMDEntriesIncremental  -- tag 268

def MarketDataIncrementalRefresh.parts (record : MarketDataIncrementalRefresh) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.group [50, 54, 56] NoMDEntriesIncremental.members NoMDEntriesIncremental.encode NoMDEntriesIncremental.within record.noMDEntriesIncremental]

def MarketDataIncrementalRefresh.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [50, 54, 56] :: NoMDEntriesIncremental.members]

theorem MarketDataIncrementalRefresh.shape (record : MarketDataIncrementalRefresh) : record.parts.map Part.tags = MarketDataIncrementalRefresh.tags := rfl

def MarketDataIncrementalRefresh.decode (tokens : List Token) : Option MarketDataIncrementalRefresh := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let noMDEntriesIncremental ← readGroup [50, 54, 56] [50, 55, 57] NoMDEntriesIncremental.members NoMDEntriesIncremental.decode tokens
  pure { mDReqID, noMDEntriesIncremental }

theorem MarketDataIncrementalRefresh.decode_agrees (record : MarketDataIncrementalRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataIncrementalRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataIncrementalRefresh.decode tokens = some record := by
  have distinct : MarketDataIncrementalRefresh.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noMDEntriesIncremental := readGroup_part [50, 54, 56] [50, 55, 57] NoMDEntriesIncremental.members NoMDEntriesIncremental.encode NoMDEntriesIncremental.within NoMDEntriesIncremental.decode NoMDEntriesIncremental.decode_encode NoMDEntriesIncremental.led record.noMDEntriesIncremental tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [MarketDataIncrementalRefresh.decode, mDReqID, noMDEntriesIncremental, some_bind] <;> rfl

structure NoEvents where
  eventType : Terminated 1  -- tag 865
  eventDate : Terminated 1  -- tag 866
  eventText : Terminated 1  -- tag 868
  eventTime : Option (Terminated 1)  -- tag 1145

def NoEvents.parts (record : NoEvents) : List Part :=
  [Part.required [56, 54, 53] record.eventType,
   Part.required [56, 54, 54] record.eventDate,
   Part.required [56, 54, 56] record.eventText,
   Part.optional [49, 49, 52, 53] record.eventTime]

def NoEvents.tags : List (List (List UInt8)) :=
  [[[56, 54, 53]], [[56, 54, 54]], [[56, 54, 56]], [[49, 49, 52, 53]]]

theorem NoEvents.shape (record : NoEvents) : record.parts.map Part.tags = NoEvents.tags := rfl

def NoEvents.decode (tokens : List Token) : Option NoEvents := do
  let eventType ← readRequired [56, 54, 53] tokens
  let eventDate ← readRequired [56, 54, 54] tokens
  let eventText ← readRequired [56, 54, 56] tokens
  let eventTime ← readOptional [49, 49, 52, 53] tokens
  pure { eventType, eventDate, eventText, eventTime }

theorem NoEvents.decode_agrees (record : NoEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEvents.decode tokens = some record := by
  have distinct : NoEvents.tags.flatten.Nodup := by decide +kernel
  have eventType := readRequired_part [56, 54, 53] record.eventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventDate := readRequired_part [56, 54, 54] record.eventDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eventText := readRequired_part [56, 54, 56] record.eventText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eventTime := readOptional_part [49, 49, 52, 53] record.eventTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoEvents.decode, eventType, eventDate, eventText, eventTime, some_bind] <;> rfl

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

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  product : Option (Terminated 1)  -- tag 460
  securityType : Terminated 1  -- tag 167
  contractMultiplier : Option (Terminated 1)  -- tag 231
  noEvents : List NoEvents  -- tag 864
  minPriceIncrement : Terminated 1  -- tag 969
  securityGroup : Terminated 1  -- tag 1151
  minTradeVol : Option (Terminated 1)  -- tag 562
  priceLimitType : Option (Terminated 1)  -- tag 1306
  lowLimitPrice : Option (Terminated 1)  -- tag 1148
  highLimitPrice : Option (Terminated 1)  -- tag 1149
  currency : Terminated 1  -- tag 15

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [52, 54, 48] record.product,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.required [57, 54, 57] record.minPriceIncrement,
   Part.required [49, 49, 53, 49] record.securityGroup,
   Part.optional [53, 54, 50] record.minTradeVol,
   Part.optional [49, 51, 48, 54] record.priceLimitType,
   Part.optional [49, 49, 52, 56] record.lowLimitPrice,
   Part.optional [49, 49, 52, 57] record.highLimitPrice,
   Part.required [49, 53] record.currency]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[52, 54, 48]], [[49, 54, 55]], [[50, 51, 49]], [56, 54, 52] :: NoEvents.members, [[57, 54, 57]], [[49, 49, 53, 49]], [[53, 54, 50]], [[49, 51, 48, 54]], [[49, 49, 52, 56]], [[49, 49, 52, 57]], [[49, 53]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let product ← readOptional [52, 54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let minPriceIncrement ← readRequired [57, 54, 57] tokens
  let securityGroup ← readRequired [49, 49, 53, 49] tokens
  let minTradeVol ← readOptional [53, 54, 50] tokens
  let priceLimitType ← readOptional [49, 51, 48, 54] tokens
  let lowLimitPrice ← readOptional [49, 49, 52, 56] tokens
  let highLimitPrice ← readOptional [49, 49, 52, 57] tokens
  let currency ← readRequired [49, 53] tokens
  pure { symbol, securityID, securityIDSource, product, securityType, contractMultiplier, noEvents, minPriceIncrement, securityGroup, minTradeVol, priceLimitType, lowLimitPrice, highLimitPrice, currency }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have product := readOptional_part [52, 54, 48] record.product tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have minPriceIncrement := readRequired_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityGroup := readRequired_part [49, 49, 53, 49] record.securityGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minTradeVol := readOptional_part [53, 54, 50] record.minTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have priceLimitType := readOptional_part [49, 51, 48, 54] record.priceLimitType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lowLimitPrice := readOptional_part [49, 49, 52, 56] record.lowLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have highLimitPrice := readOptional_part [49, 49, 52, 57] record.highLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, product, securityType, contractMultiplier, noEvents, minPriceIncrement, securityGroup, minTradeVol, priceLimitType, lowLimitPrice, highLimitPrice, currency, some_bind] <;> rfl

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
  noRelatedSym : List NoRelatedSym  -- tag 146
  securityReqID : Terminated 1  -- tag 320
  securityResponseID : Terminated 1  -- tag 322
  securityRequestResult : Terminated 1  -- tag 560

def SecurityList.parts (record : SecurityList) : List Part :=
  [Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 50] record.securityResponseID,
   Part.required [53, 54, 48] record.securityRequestResult]

def SecurityList.tags : List (List (List UInt8)) :=
  [[49, 52, 54] :: NoRelatedSym.members, [[51, 50, 48]], [[51, 50, 50]], [[53, 54, 48]]]

theorem SecurityList.shape (record : SecurityList) : record.parts.map Part.tags = SecurityList.tags := rfl

def SecurityList.decode (tokens : List Token) : Option SecurityList := do
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseID ← readRequired [51, 50, 50] tokens
  let securityRequestResult ← readRequired [53, 54, 48] tokens
  pure { noRelatedSym, securityReqID, securityResponseID, securityRequestResult }

theorem SecurityList.decode_agrees (record : SecurityList) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityList.decode tokens = some record := by
  have distinct : SecurityList.tags.flatten.Nodup := by decide +kernel
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityResponseID := readRequired_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityRequestResult := readRequired_part [53, 54, 48] record.securityRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityList.decode, noRelatedSym, securityReqID, securityResponseID, securityRequestResult, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | reject (header : Header) (r0 : Reject)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh)
  | marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh)
  | securityList (header : Header) (r0 : SecurityList)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataSnapshotFullRefresh header r0 => ⟨[51, 53], ⟨[87], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataIncrementalRefresh header r0 => ⟨[51, 53], ⟨[88], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityList header r0 => ⟨[51, 53], ⟨[121], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [87] then
        if known (Header.tags ++ MarketDataSnapshotFullRefresh.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataSnapshotFullRefresh.decode rest
          pure (.marketDataSnapshotFullRefresh header r0)
        else none
      else if token.value.val = [88] then
        if known (Header.tags ++ MarketDataIncrementalRefresh.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataIncrementalRefresh.decode rest
          pure (.marketDataIncrementalRefresh header r0)
        else none
      else if token.value.val = [121] then
        if known (Header.tags ++ SecurityList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityList.decode rest
          pure (.securityList header r0)
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

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh) :
    Message.decode (Message.tokens (.marketDataSnapshotFullRefresh header r0)) = some (.marketDataSnapshotFullRefresh header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshotFullRefresh.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataSnapshotFullRefresh.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshotFullRefresh.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataSnapshotFullRefresh.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decode (Message.tokens (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataIncrementalRefresh.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataIncrementalRefresh.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityList (header : Header) (r0 : SecurityList) :
    Message.decode (Message.tokens (.securityList header r0)) = some (.securityList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | reject header r0 => exact Message.decode_reject header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decode_marketDataSnapshotFullRefresh header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decode_marketDataIncrementalRefresh header r0
  | securityList header r0 => exact Message.decode_securityList header r0

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

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh) :
    Message.decodeBytes (Message.encode (.marketDataSnapshotFullRefresh header r0)) = some (.marketDataSnapshotFullRefresh header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[87], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDataSnapshotFullRefresh.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataSnapshotFullRefresh header r0

theorem Message.decodeBytes_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decodeBytes (Message.encode (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[88], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MarketDataIncrementalRefresh.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataIncrementalRefresh header r0

theorem Message.decodeBytes_securityList (header : Header) (r0 : SecurityList) :
    Message.decodeBytes (Message.encode (.securityList header r0)) = some (.securityList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[121], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityList header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decodeBytes_marketDataSnapshotFullRefresh header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decodeBytes_marketDataIncrementalRefresh header r0
  | securityList header r0 => exact Message.decodeBytes_securityList header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.ElectronxElectricderivativesMarketdataFixV202601071Exchange
