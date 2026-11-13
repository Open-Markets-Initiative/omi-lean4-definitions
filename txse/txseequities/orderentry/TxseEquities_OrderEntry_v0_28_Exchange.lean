import Wire

/-!
# Texas Stock Exchange Order Entry v0.28, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.TxseTxseequitiesOrderentryFixV028Exchange

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  sendingTime : Option (Terminated 1)  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [49, 49, 53] record.onBehalfOfCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 57]], [[53, 54]], [[53, 50]], [[52, 51]], [[49, 49, 53]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  pure { msgSeqNum, senderCompID, targetCompID, sendingTime, possDupFlag, onBehalfOfCompID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, senderCompID, targetCompID, sendingTime, possDupFlag, onBehalfOfCompID, some_bind] <;> rfl

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
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789
  password : Terminated 1  -- tag 554
  encryptMethod : Option (Terminated 1)  -- tag 98
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  heartBtInt : Option (Terminated 1)  -- tag 108
  defaultApplVerID : Option (Terminated 1)  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 56] record.encryptMethod,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [49, 48, 56] record.heartBtInt,
   Part.optional [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[55, 56, 57]], [[53, 53, 52]], [[57, 56]], [[49, 52, 49]], [[49, 48, 56]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  let password ← readRequired [53, 53, 52] tokens
  let encryptMethod ← readOptional [57, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let heartBtInt ← readOptional [49, 48, 56] tokens
  let defaultApplVerID ← readOptional [49, 49, 51, 55] tokens
  pure { nextExpectedMsgSeqNum, password, encryptMethod, resetSeqNumFlag, heartBtInt, defaultApplVerID }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have encryptMethod := readOptional_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have heartBtInt := readOptional_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have defaultApplVerID := readOptional_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Logon.decode, nextExpectedMsgSeqNum, password, encryptMethod, resetSeqNumFlag, heartBtInt, defaultApplVerID, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  pure { refSeqNum, refMsgType, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refMsgType, sessionRejectReason, some_bind] <;> rfl

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

structure ExecutionReport where
  transactTime : Terminated 1  -- tag 60
  ordStatus : Terminated 1  -- tag 39
  clOrdID : Terminated 1  -- tag 11
  execID : Terminated 1  -- tag 17
  symbol : Terminated 1  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  side : Terminated 1  -- tag 54
  clientID : Terminated 1  -- tag 109
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [51, 57] record.ordStatus,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 55] record.execID,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [53, 52] record.side,
   Part.required [49, 48, 57] record.clientID,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[51, 57]], [[49, 49]], [[49, 55]], [[53, 53]], [[54, 53]], [[53, 52]], [[49, 48, 57]], [[49, 53, 49]], [[49, 52]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let transactTime ← readRequired [54, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let side ← readRequired [53, 52] tokens
  let clientID ← readRequired [49, 48, 57] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  pure { transactTime, ordStatus, clOrdID, execID, symbol, symbolSfx, side, clientID, leavesQty, cumQty }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clientID := readRequired_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [ExecutionReport.decode, transactTime, ordStatus, clOrdID, execID, symbol, symbolSfx, side, clientID, leavesQty, cumQty, some_bind] <;> rfl

structure ExecutionReportNew where
  ordType : Terminated 1  -- tag 40
  orderID : Terminated 1  -- tag 37
  locateReqd : Terminated 1  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  timeInForce : Terminated 1  -- tag 59
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Terminated 1  -- tag 9005
  orderCapacity : Terminated 1  -- tag 528
  memberGroup : Terminated 1  -- tag 9004
  selfMatchScope : Terminated 1  -- tag 8001
  selfMatchPreventionInstruction : Terminated 1  -- tag 2964
  priceSlideInstruction : Terminated 1  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  minQty : Option (Terminated 1)  -- tag 110
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMinIncr : Option (Terminated 1)  -- tag 1087
  maxReplenishTimeRange : Option (Terminated 1)  -- tag 9001
  expireTime : Option (Terminated 1)  -- tag 126
  userData : Option (Terminated 1)  -- tag 9002
  rankPrice : Option (Terminated 1)  -- tag 9008
  currentDisplayPrice : Option (Terminated 1)  -- tag 2828

def ExecutionReportNew.parts (record : ExecutionReportNew) : List Part :=
  [Part.required [52, 48] record.ordType,
   Part.required [51, 55] record.orderID,
   Part.required [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [53, 57] record.timeInForce,
   Part.optional [49, 56] record.execInst,
   Part.required [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.required [57, 48, 48, 52] record.memberGroup,
   Part.required [56, 48, 48, 49] record.selfMatchScope,
   Part.required [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.required [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 55] record.displayMinIncr,
   Part.optional [57, 48, 48, 49] record.maxReplenishTimeRange,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [57, 48, 48, 50] record.userData,
   Part.optional [57, 48, 48, 56] record.rankPrice,
   Part.optional [50, 56, 50, 56] record.currentDisplayPrice]

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  [[[52, 48]], [[51, 55]], [[49, 49, 52]], [[57, 48, 48, 48]], [[52, 52]], [[51, 56]], [[53, 57]], [[49, 56]], [[57, 48, 48, 53]], [[53, 50, 56]], [[57, 48, 48, 52]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 48]], [[49, 49, 51, 56]], [[49, 48, 56, 55]], [[57, 48, 48, 49]], [[49, 50, 54]], [[57, 48, 48, 50]], [[57, 48, 48, 56]], [[50, 56, 50, 56]]]

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (tokens : List Token) : Option ExecutionReportNew := do
  let ordType ← readRequired [52, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let locateReqd ← readRequired [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readRequired [57, 48, 48, 53] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let memberGroup ← readRequired [57, 48, 48, 52] tokens
  let selfMatchScope ← readRequired [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readRequired [50, 57, 54, 52] tokens
  let priceSlideInstruction ← readRequired [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMinIncr ← readOptional [49, 48, 56, 55] tokens
  let maxReplenishTimeRange ← readOptional [57, 48, 48, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let userData ← readOptional [57, 48, 48, 50] tokens
  let rankPrice ← readOptional [57, 48, 48, 56] tokens
  let currentDisplayPrice ← readOptional [50, 56, 50, 56] tokens
  pure { ordType, orderID, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, orderCapacity, memberGroup, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime, userData, rankPrice, currentDisplayPrice }

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  have distinct : ExecutionReportNew.tags.flatten.Nodup := by decide +kernel
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have locateReqd := readRequired_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readRequired_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have memberGroup := readRequired_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have selfMatchScope := readRequired_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have selfMatchPreventionInstruction := readRequired_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have priceSlideInstruction := readRequired_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have displayMinIncr := readOptional_part [49, 48, 56, 55] record.displayMinIncr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maxReplenishTimeRange := readOptional_part [57, 48, 48, 49] record.maxReplenishTimeRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have userData := readOptional_part [57, 48, 48, 50] record.userData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have rankPrice := readOptional_part [57, 48, 48, 56] record.rankPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have currentDisplayPrice := readOptional_part [50, 56, 50, 56] record.currentDisplayPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [ExecutionReportNew.decode, ordType, orderID, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, orderCapacity, memberGroup, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime, userData, rankPrice, currentDisplayPrice, some_bind] <;> rfl

structure ExecutionReportRejected where
  ordType : Terminated 1  -- tag 40
  locateReqd : Terminated 1  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  timeInForce : Terminated 1  -- tag 59
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Terminated 1  -- tag 9005
  orderCapacity : Terminated 1  -- tag 528
  memberGroup : Option (Terminated 1)  -- tag 9004
  selfMatchScope : Option (Terminated 1)  -- tag 8001
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 2964
  priceSlideInstruction : Option (Terminated 1)  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  minQty : Option (Terminated 1)  -- tag 110
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMinIncr : Option (Terminated 1)  -- tag 1087
  maxReplenishTimeRange : Option (Terminated 1)  -- tag 9001
  expireTime : Option (Terminated 1)  -- tag 126
  userData : Option (Terminated 1)  -- tag 9002
  ordRejReason : Terminated 1  -- tag 103

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.required [52, 48] record.ordType,
   Part.required [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [53, 57] record.timeInForce,
   Part.optional [49, 56] record.execInst,
   Part.required [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [57, 48, 48, 52] record.memberGroup,
   Part.optional [56, 48, 48, 49] record.selfMatchScope,
   Part.optional [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.optional [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 55] record.displayMinIncr,
   Part.optional [57, 48, 48, 49] record.maxReplenishTimeRange,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [57, 48, 48, 50] record.userData,
   Part.required [49, 48, 51] record.ordRejReason]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[52, 48]], [[49, 49, 52]], [[57, 48, 48, 48]], [[52, 52]], [[51, 56]], [[53, 57]], [[49, 56]], [[57, 48, 48, 53]], [[53, 50, 56]], [[57, 48, 48, 52]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 48]], [[49, 49, 51, 56]], [[49, 48, 56, 55]], [[57, 48, 48, 49]], [[49, 50, 54]], [[57, 48, 48, 50]], [[49, 48, 51]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let ordType ← readRequired [52, 48] tokens
  let locateReqd ← readRequired [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readRequired [57, 48, 48, 53] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let memberGroup ← readOptional [57, 48, 48, 52] tokens
  let selfMatchScope ← readOptional [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readOptional [50, 57, 54, 52] tokens
  let priceSlideInstruction ← readOptional [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMinIncr ← readOptional [49, 48, 56, 55] tokens
  let maxReplenishTimeRange ← readOptional [57, 48, 48, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let userData ← readOptional [57, 48, 48, 50] tokens
  let ordRejReason ← readRequired [49, 48, 51] tokens
  pure { ordType, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, orderCapacity, memberGroup, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime, userData, ordRejReason }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have locateReqd := readRequired_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readRequired_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have memberGroup := readOptional_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchScope := readOptional_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have priceSlideInstruction := readOptional_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have displayMinIncr := readOptional_part [49, 48, 56, 55] record.displayMinIncr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maxReplenishTimeRange := readOptional_part [57, 48, 48, 49] record.maxReplenishTimeRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have userData := readOptional_part [57, 48, 48, 50] record.userData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, ordType, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, orderCapacity, memberGroup, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime, userData, ordRejReason, some_bind] <;> rfl

structure ExecutionReportCanceled where
  origClOrdID : Terminated 1  -- tag 41
  orderID : Terminated 1  -- tag 37
  cxlQty : Terminated 1  -- tag 84
  cancelReason : Terminated 1  -- tag 8003
  execRestatementReason : Option (Terminated 1)  -- tag 378
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [56, 52] record.cxlQty,
   Part.required [56, 48, 48, 51] record.cancelReason,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[51, 55]], [[56, 52]], [[56, 48, 48, 51]], [[51, 55, 56]], [[51, 49]], [[51, 50]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let cxlQty ← readRequired [56, 52] tokens
  let cancelReason ← readRequired [56, 48, 48, 51] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  pure { origClOrdID, orderID, cxlQty, cancelReason, execRestatementReason, lastPx, lastQty }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cxlQty := readRequired_part [56, 52] record.cxlQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cancelReason := readRequired_part [56, 48, 48, 51] record.cancelReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, origClOrdID, orderID, cxlQty, cancelReason, execRestatementReason, lastPx, lastQty, some_bind] <;> rfl

structure ExecutionReportReplaced where
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  orderID : Terminated 1  -- tag 37
  locateReqd : Terminated 1  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  timeInForce : Terminated 1  -- tag 59
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Terminated 1  -- tag 9005
  selfMatchScope : Terminated 1  -- tag 8001
  selfMatchPreventionInstruction : Terminated 1  -- tag 2964
  priceSlideInstruction : Terminated 1  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  displayQty : Option (Terminated 1)  -- tag 1138
  rankPrice : Option (Terminated 1)  -- tag 9008
  currentDisplayPrice : Option (Terminated 1)  -- tag 2828

def ExecutionReportReplaced.parts (record : ExecutionReportReplaced) : List Part :=
  [Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [53, 57] record.timeInForce,
   Part.optional [49, 56] record.execInst,
   Part.required [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.required [56, 48, 48, 49] record.selfMatchScope,
   Part.required [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.required [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [57, 48, 48, 56] record.rankPrice,
   Part.optional [50, 56, 50, 56] record.currentDisplayPrice]

def ExecutionReportReplaced.tags : List (List (List UInt8)) :=
  [[[52, 48]], [[52, 49]], [[51, 55]], [[49, 49, 52]], [[57, 48, 48, 48]], [[52, 52]], [[51, 56]], [[53, 57]], [[49, 56]], [[57, 48, 48, 53]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 51, 56]], [[57, 48, 48, 56]], [[50, 56, 50, 56]]]

theorem ExecutionReportReplaced.shape (record : ExecutionReportReplaced) : record.parts.map Part.tags = ExecutionReportReplaced.tags := rfl

def ExecutionReportReplaced.decode (tokens : List Token) : Option ExecutionReportReplaced := do
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let locateReqd ← readRequired [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readRequired [57, 48, 48, 53] tokens
  let selfMatchScope ← readRequired [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readRequired [50, 57, 54, 52] tokens
  let priceSlideInstruction ← readRequired [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let rankPrice ← readOptional [57, 48, 48, 56] tokens
  let currentDisplayPrice ← readOptional [50, 56, 50, 56] tokens
  pure { ordType, origClOrdID, orderID, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty, rankPrice, currentDisplayPrice }

theorem ExecutionReportReplaced.decode_agrees (record : ExecutionReportReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplaced.decode tokens = some record := by
  have distinct : ExecutionReportReplaced.tags.flatten.Nodup := by decide +kernel
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have locateReqd := readRequired_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readRequired_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchScope := readRequired_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have selfMatchPreventionInstruction := readRequired_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have priceSlideInstruction := readRequired_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have rankPrice := readOptional_part [57, 48, 48, 56] record.rankPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have currentDisplayPrice := readOptional_part [50, 56, 50, 56] record.currentDisplayPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [ExecutionReportReplaced.decode, ordType, origClOrdID, orderID, locateReqd, locateBroker, price, orderQty, timeInForce, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty, rankPrice, currentDisplayPrice, some_bind] <;> rfl

structure ExecutionReportTrade where
  orderID : Terminated 1  -- tag 37
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32
  lastLiquidityInd : Terminated 1  -- tag 851
  tradeLiquidityIndicator : Terminated 1  -- tag 9730

def ExecutionReportTrade.parts (record : ExecutionReportTrade) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.required [56, 53, 49] record.lastLiquidityInd,
   Part.required [57, 55, 51, 48] record.tradeLiquidityIndicator]

def ExecutionReportTrade.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[51, 49]], [[51, 50]], [[56, 53, 49]], [[57, 55, 51, 48]]]

theorem ExecutionReportTrade.shape (record : ExecutionReportTrade) : record.parts.map Part.tags = ExecutionReportTrade.tags := rfl

def ExecutionReportTrade.decode (tokens : List Token) : Option ExecutionReportTrade := do
  let orderID ← readRequired [51, 55] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastLiquidityInd ← readRequired [56, 53, 49] tokens
  let tradeLiquidityIndicator ← readRequired [57, 55, 51, 48] tokens
  pure { orderID, lastPx, lastQty, lastLiquidityInd, tradeLiquidityIndicator }

theorem ExecutionReportTrade.decode_agrees (record : ExecutionReportTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTrade.decode tokens = some record := by
  have distinct : ExecutionReportTrade.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastLiquidityInd := readRequired_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeLiquidityIndicator := readRequired_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportTrade.decode, orderID, lastPx, lastQty, lastLiquidityInd, tradeLiquidityIndicator, some_bind] <;> rfl

structure ExecutionReportRestated where
  orderID : Terminated 1  -- tag 37
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  execRestatementReason : Terminated 1  -- tag 378
  displayQty : Terminated 1  -- tag 1138
  rankPrice : Terminated 1  -- tag 9008
  currentDisplayPrice : Option (Terminated 1)  -- tag 2828
  cxlQty : Terminated 1  -- tag 84
  cancelReason : Option (Terminated 1)  -- tag 8003
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 55, 56] record.execRestatementReason,
   Part.required [49, 49, 51, 56] record.displayQty,
   Part.required [57, 48, 48, 56] record.rankPrice,
   Part.optional [50, 56, 50, 56] record.currentDisplayPrice,
   Part.required [56, 52] record.cxlQty,
   Part.optional [56, 48, 48, 51] record.cancelReason,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[52, 52]], [[51, 56]], [[51, 55, 56]], [[49, 49, 51, 56]], [[57, 48, 48, 56]], [[50, 56, 50, 56]], [[56, 52]], [[56, 48, 48, 51]], [[51, 49]], [[51, 50]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let orderID ← readRequired [51, 55] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let execRestatementReason ← readRequired [51, 55, 56] tokens
  let displayQty ← readRequired [49, 49, 51, 56] tokens
  let rankPrice ← readRequired [57, 48, 48, 56] tokens
  let currentDisplayPrice ← readOptional [50, 56, 50, 56] tokens
  let cxlQty ← readRequired [56, 52] tokens
  let cancelReason ← readOptional [56, 48, 48, 51] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  pure { orderID, price, orderQty, execRestatementReason, displayQty, rankPrice, currentDisplayPrice, cxlQty, cancelReason, lastPx, lastQty }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execRestatementReason := readRequired_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have displayQty := readRequired_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have rankPrice := readRequired_part [57, 48, 48, 56] record.rankPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have currentDisplayPrice := readOptional_part [50, 56, 50, 56] record.currentDisplayPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cxlQty := readRequired_part [56, 52] record.cxlQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have cancelReason := readOptional_part [56, 48, 48, 51] record.cancelReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, orderID, price, orderQty, execRestatementReason, displayQty, rankPrice, currentDisplayPrice, cxlQty, cancelReason, lastPx, lastQty, some_bind] <;> rfl

structure OrderCancelReject where
  transactTime : Terminated 1  -- tag 60
  ordStatus : Terminated 1  -- tag 39
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  cxlRejReason : Terminated 1  -- tag 102

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [51, 57] record.ordStatus,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [49, 48, 50] record.cxlRejReason]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[51, 57]], [[49, 49]], [[52, 49]], [[51, 55]], [[49, 48, 50]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let transactTime ← readRequired [54, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let cxlRejReason ← readRequired [49, 48, 50] tokens
  pure { transactTime, ordStatus, clOrdID, origClOrdID, orderID, cxlRejReason }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejReason := readRequired_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderCancelReject.decode, transactTime, ordStatus, clOrdID, origClOrdID, orderID, cxlRejReason, some_bind] <;> rfl

structure OrderCancelRejectOrderCancelReject

def OrderCancelRejectOrderCancelReject.parts (_ : OrderCancelRejectOrderCancelReject) : List Part :=
  []

def OrderCancelRejectOrderCancelReject.tags : List (List (List UInt8)) :=
  []

theorem OrderCancelRejectOrderCancelReject.shape (record : OrderCancelRejectOrderCancelReject) : record.parts.map Part.tags = OrderCancelRejectOrderCancelReject.tags := rfl

def OrderCancelRejectOrderCancelReject.decode (_ : List Token) : Option OrderCancelRejectOrderCancelReject := some {}

theorem OrderCancelRejectOrderCancelReject.decode_agrees (record : OrderCancelRejectOrderCancelReject) (tokens : List Token)
    (_ : ∀ tags ∈ OrderCancelRejectOrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRejectOrderCancelReject.decode tokens = some record := by
  rfl

structure OrderCancelRejectOrderReplaceReject where
  side : Terminated 1  -- tag 54
  locateReqd : Terminated 1  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  price : Option (Terminated 1)  -- tag 44
  orderQty : Option (Terminated 1)  -- tag 38
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Terminated 1  -- tag 9005
  selfMatchScope : Option (Terminated 1)  -- tag 8001
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 2964
  priceSlideInstruction : Option (Terminated 1)  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  displayQty : Option (Terminated 1)  -- tag 1138

def OrderCancelRejectOrderReplaceReject.parts (record : OrderCancelRejectOrderReplaceReject) : List Part :=
  [Part.required [53, 52] record.side,
   Part.required [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.optional [52, 52] record.price,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 56] record.execInst,
   Part.required [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.optional [56, 48, 48, 49] record.selfMatchScope,
   Part.optional [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.optional [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 51, 56] record.displayQty]

def OrderCancelRejectOrderReplaceReject.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 49, 52]], [[57, 48, 48, 48]], [[52, 52]], [[51, 56]], [[49, 56]], [[57, 48, 48, 53]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 51, 56]]]

theorem OrderCancelRejectOrderReplaceReject.shape (record : OrderCancelRejectOrderReplaceReject) : record.parts.map Part.tags = OrderCancelRejectOrderReplaceReject.tags := rfl

def OrderCancelRejectOrderReplaceReject.decode (tokens : List Token) : Option OrderCancelRejectOrderReplaceReject := do
  let side ← readRequired [53, 52] tokens
  let locateReqd ← readRequired [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readRequired [57, 48, 48, 53] tokens
  let selfMatchScope ← readOptional [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readOptional [50, 57, 54, 52] tokens
  let priceSlideInstruction ← readOptional [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  pure { side, locateReqd, locateBroker, price, orderQty, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty }

theorem OrderCancelRejectOrderReplaceReject.decode_agrees (record : OrderCancelRejectOrderReplaceReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRejectOrderReplaceReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRejectOrderReplaceReject.decode tokens = some record := by
  have distinct : OrderCancelRejectOrderReplaceReject.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have locateReqd := readRequired_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readRequired_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have selfMatchScope := readOptional_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have priceSlideInstruction := readOptional_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [OrderCancelRejectOrderReplaceReject.decode, side, locateReqd, locateBroker, price, orderQty, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty, some_bind] <;> rfl

structure OrderMassCancelReport where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11

def OrderMassCancelReport.parts (record : OrderMassCancelReport) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID]

def OrderMassCancelReport.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]]]

theorem OrderMassCancelReport.shape (record : OrderMassCancelReport) : record.parts.map Part.tags = OrderMassCancelReport.tags := rfl

def OrderMassCancelReport.decode (tokens : List Token) : Option OrderMassCancelReport := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  pure { transactTime, clOrdID }

theorem OrderMassCancelReport.decode_agrees (record : OrderMassCancelReport) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReport.decode tokens = some record := by
  have distinct : OrderMassCancelReport.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [OrderMassCancelReport.decode, transactTime, clOrdID, some_bind] <;> rfl

structure OrderMassCancelReportAccepted where
  massActionReportID : Terminated 1  -- tag 1369
  massCancelRequestType : Terminated 1  -- tag 530
  clientID : Option (Terminated 1)  -- tag 109
  refCompID : Option (Terminated 1)  -- tag 930
  memberGroup : Option (Terminated 1)  -- tag 9004
  origClOrdID : Option (Terminated 1)  -- tag 41

def OrderMassCancelReportAccepted.parts (record : OrderMassCancelReportAccepted) : List Part :=
  [Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 51, 48] record.refCompID,
   Part.optional [57, 48, 48, 52] record.memberGroup,
   Part.optional [52, 49] record.origClOrdID]

def OrderMassCancelReportAccepted.tags : List (List (List UInt8)) :=
  [[[49, 51, 54, 57]], [[53, 51, 48]], [[49, 48, 57]], [[57, 51, 48]], [[57, 48, 48, 52]], [[52, 49]]]

theorem OrderMassCancelReportAccepted.shape (record : OrderMassCancelReportAccepted) : record.parts.map Part.tags = OrderMassCancelReportAccepted.tags := rfl

def OrderMassCancelReportAccepted.decode (tokens : List Token) : Option OrderMassCancelReportAccepted := do
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let refCompID ← readOptional [57, 51, 48] tokens
  let memberGroup ← readOptional [57, 48, 48, 52] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  pure { massActionReportID, massCancelRequestType, clientID, refCompID, memberGroup, origClOrdID }

theorem OrderMassCancelReportAccepted.decode_agrees (record : OrderMassCancelReportAccepted) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReportAccepted.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReportAccepted.decode tokens = some record := by
  have distinct : OrderMassCancelReportAccepted.tags.flatten.Nodup := by decide +kernel
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refCompID := readOptional_part [57, 51, 48] record.refCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have memberGroup := readOptional_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderMassCancelReportAccepted.decode, massActionReportID, massCancelRequestType, clientID, refCompID, memberGroup, origClOrdID, some_bind] <;> rfl

structure OrderMassCancelReportRejected where
  massCancelRequestType : Terminated 1  -- tag 530
  massCancelRejectReason : Terminated 1  -- tag 532
  clientID : Option (Terminated 1)  -- tag 109
  refCompID : Option (Terminated 1)  -- tag 930
  memberGroup : Option (Terminated 1)  -- tag 9004
  origClOrdID : Option (Terminated 1)  -- tag 41

def OrderMassCancelReportRejected.parts (record : OrderMassCancelReportRejected) : List Part :=
  [Part.required [53, 51, 48] record.massCancelRequestType,
   Part.required [53, 51, 50] record.massCancelRejectReason,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 51, 48] record.refCompID,
   Part.optional [57, 48, 48, 52] record.memberGroup,
   Part.optional [52, 49] record.origClOrdID]

def OrderMassCancelReportRejected.tags : List (List (List UInt8)) :=
  [[[53, 51, 48]], [[53, 51, 50]], [[49, 48, 57]], [[57, 51, 48]], [[57, 48, 48, 52]], [[52, 49]]]

theorem OrderMassCancelReportRejected.shape (record : OrderMassCancelReportRejected) : record.parts.map Part.tags = OrderMassCancelReportRejected.tags := rfl

def OrderMassCancelReportRejected.decode (tokens : List Token) : Option OrderMassCancelReportRejected := do
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let massCancelRejectReason ← readRequired [53, 51, 50] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let refCompID ← readOptional [57, 51, 48] tokens
  let memberGroup ← readOptional [57, 48, 48, 52] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  pure { massCancelRequestType, massCancelRejectReason, clientID, refCompID, memberGroup, origClOrdID }

theorem OrderMassCancelReportRejected.decode_agrees (record : OrderMassCancelReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReportRejected.decode tokens = some record := by
  have distinct : OrderMassCancelReportRejected.tags.flatten.Nodup := by decide +kernel
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massCancelRejectReason := readRequired_part [53, 51, 50] record.massCancelRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refCompID := readOptional_part [57, 51, 48] record.refCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have memberGroup := readOptional_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderMassCancelReportRejected.decode, massCancelRequestType, massCancelRejectReason, clientID, refCompID, memberGroup, origClOrdID, some_bind] <;> rfl

structure OrderMassCancelReportComplete where
  massActionReportID : Terminated 1  -- tag 1369
  totalAffectedOrders : Terminated 1  -- tag 533

def OrderMassCancelReportComplete.parts (record : OrderMassCancelReportComplete) : List Part :=
  [Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [53, 51, 51] record.totalAffectedOrders]

def OrderMassCancelReportComplete.tags : List (List (List UInt8)) :=
  [[[49, 51, 54, 57]], [[53, 51, 51]]]

theorem OrderMassCancelReportComplete.shape (record : OrderMassCancelReportComplete) : record.parts.map Part.tags = OrderMassCancelReportComplete.tags := rfl

def OrderMassCancelReportComplete.decode (tokens : List Token) : Option OrderMassCancelReportComplete := do
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let totalAffectedOrders ← readRequired [53, 51, 51] tokens
  pure { massActionReportID, totalAffectedOrders }

theorem OrderMassCancelReportComplete.decode_agrees (record : OrderMassCancelReportComplete) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReportComplete.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReportComplete.decode tokens = some record := by
  have distinct : OrderMassCancelReportComplete.tags.flatten.Nodup := by decide +kernel
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have totalAffectedOrders := readRequired_part [53, 51, 51] record.totalAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [OrderMassCancelReportComplete.decode, massActionReportID, totalAffectedOrders, some_bind] <;> rfl

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | orderCancelRejectOrderCancelReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderCancelReject)
  | orderCancelRejectOrderReplaceReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderReplaceReject)
  | orderMassCancelReportAccepted (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportAccepted)
  | orderMassCancelReportRejected (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportRejected)
  | orderMassCancelReportComplete (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportComplete)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportTrade header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .orderCancelRejectOrderCancelReject header r0 r1 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[49], by decide⟩] ++ r1.parts)
  | .orderCancelRejectOrderReplaceReject header r0 r1 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[50], by decide⟩] ++ r1.parts)
  | .orderMassCancelReportAccepted header r0 r1 => ⟨[51, 53], ⟨[114], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩] ++ r1.parts)
  | .orderMassCancelReportRejected header r0 r1 => ⟨[51, 53], ⟨[114], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[48], by decide⟩] ++ r1.parts)
  | .orderMassCancelReportComplete header r0 r1 => ⟨[51, 53], ⟨[114], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩] ++ r1.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [48] then
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
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else if token.value.val = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNew.decode rest
              pure (.executionReportNew header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCanceled.decode rest
              pure (.executionReportCanceled header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportReplaced.decode rest
              pure (.executionReportReplaced header r0 r1)
            else none
          else if key.val = [70] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTrade.decode rest
              pure (.executionReportTrade header r0 r1)
            else none
          else if key.val = [68] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRestated.decode rest
              pure (.executionReportRestated header r0 r1)
            else none
          else none
      else if token.value.val = [57] then
        match readRequired [52, 51, 52] rest with
        | none => none
        | some key =>
          if key.val = [49] then
            if known (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderCancelReject.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderCancelReject.decode rest
              let r1 ← OrderCancelRejectOrderCancelReject.decode rest
              pure (.orderCancelRejectOrderCancelReject header r0 r1)
            else none
          else if key.val = [50] then
            if known (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderReplaceReject.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderCancelReject.decode rest
              let r1 ← OrderCancelRejectOrderReplaceReject.decode rest
              pure (.orderCancelRejectOrderReplaceReject header r0 r1)
            else none
          else none
      else if token.value.val = [114] then
        match readRequired [53, 51, 49] rest with
        | none => none
        | some key =>
          if key.val = [49, 48, 48] then
            if known (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportAccepted.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderMassCancelReport.decode rest
              let r1 ← OrderMassCancelReportAccepted.decode rest
              pure (.orderMassCancelReportAccepted header r0 r1)
            else none
          else if key.val = [48] then
            if known (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderMassCancelReport.decode rest
              let r1 ← OrderMassCancelReportRejected.decode rest
              pure (.orderMassCancelReportRejected header r0 r1)
            else none
          else if key.val = [49, 48, 49] then
            if known (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportComplete.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OrderMassCancelReport.decode rest
              let r1 ← OrderMassCancelReportComplete.decode rest
              pure (.orderMassCancelReportComplete header r0 r1)
            else none
          else none
      else none
    else none

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
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

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decode (Message.tokens (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decode (Message.tokens (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCanceled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCanceled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decode (Message.tokens (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportReplaced.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportReplaced.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportReplaced.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decode (Message.tokens (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[70], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decode (Message.tokens (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[68], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRestated.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRestated.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRestated.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRejectOrderCancelReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelRejectOrderCancelReject header r0 r1)) = some (.orderCancelRejectOrderCancelReject header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [52, 51, 52] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [52, 51, 52] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (OrderCancelReject.tags) ([[[52, 51, 52]]] ++ OrderCancelRejectOrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [52, 51, 52] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [52, 51, 52] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ OrderCancelReject.tags) ([[[52, 51, 52]]]) (OrderCancelRejectOrderCancelReject.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRejectOrderCancelReject.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]]) (OrderCancelRejectOrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRejectOrderReplaceReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderReplaceReject) :
    Message.decode (Message.tokens (.orderCancelRejectOrderReplaceReject header r0 r1)) = some (.orderCancelRejectOrderReplaceReject header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [52, 51, 52] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderReplaceReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [52, 51, 52] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (OrderCancelReject.tags) ([[[52, 51, 52]]] ++ OrderCancelRejectOrderReplaceReject.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [52, 51, 52] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [52, 51, 52] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ OrderCancelReject.tags) ([[[52, 51, 52]]]) (OrderCancelRejectOrderReplaceReject.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderCancelRejectOrderReplaceReject.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]]) (OrderCancelRejectOrderReplaceReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderReplaceReject.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReportAccepted (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportAccepted) :
    Message.decode (Message.tokens (.orderMassCancelReportAccepted header r0 r1)) = some (.orderMassCancelReportAccepted header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportAccepted.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩] ++ r1.parts) (Header.tags) (OrderMassCancelReport.tags) ([[[53, 51, 49]]] ++ OrderMassCancelReportAccepted.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 51, 49] ⟨[49, 48, 48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩]) (r1.parts) (Header.tags ++ OrderMassCancelReport.tags) ([[[53, 51, 49]]]) (OrderMassCancelReportAccepted.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderMassCancelReportAccepted.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]]) (OrderMassCancelReportAccepted.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportAccepted.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReportRejected (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportRejected) :
    Message.decode (Message.tokens (.orderMassCancelReportRejected header r0 r1)) = some (.orderMassCancelReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 51, 49] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 51, 49] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (OrderMassCancelReport.tags) ([[[53, 51, 49]]] ++ OrderMassCancelReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 51, 49] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 51, 49] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ OrderMassCancelReport.tags) ([[[53, 51, 49]]]) (OrderMassCancelReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderMassCancelReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]]) (OrderMassCancelReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReportComplete (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportComplete) :
    Message.decode (Message.tokens (.orderMassCancelReportComplete header r0 r1)) = some (.orderMassCancelReportComplete header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportComplete.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩] ++ r1.parts) (Header.tags) (OrderMassCancelReport.tags) ([[[53, 51, 49]]] ++ OrderMassCancelReportComplete.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 51, 49] ⟨[49, 48, 49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩]) (r1.parts) (Header.tags ++ OrderMassCancelReport.tags) ([[[53, 51, 49]]]) (OrderMassCancelReportComplete.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OrderMassCancelReportComplete.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]]) (OrderMassCancelReportComplete.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportComplete.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decode_executionReportTrade header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | orderCancelRejectOrderCancelReject header r0 r1 => exact Message.decode_orderCancelRejectOrderCancelReject header r0 r1
  | orderCancelRejectOrderReplaceReject header r0 r1 => exact Message.decode_orderCancelRejectOrderReplaceReject header r0 r1
  | orderMassCancelReportAccepted header r0 r1 => exact Message.decode_orderMassCancelReportAccepted header r0 r1
  | orderMassCancelReportRejected header r0 r1 => exact Message.decode_orderMassCancelReportRejected header r0 r1
  | orderMassCancelReportComplete header r0 r1 => exact Message.decode_orderMassCancelReportComplete header r0 r1

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

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

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decodeBytes (Message.encode (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplaced header r0 r1

theorem Message.decodeBytes_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decodeBytes (Message.encode (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTrade header r0 r1

theorem Message.decodeBytes_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decodeBytes (Message.encode (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRestated header r0 r1

theorem Message.decodeBytes_orderCancelRejectOrderCancelReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelRejectOrderCancelReject header r0 r1)) = some (.orderCancelRejectOrderCancelReject header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRejectOrderCancelReject header r0 r1

theorem Message.decodeBytes_orderCancelRejectOrderReplaceReject (header : Header) (r0 : OrderCancelReject) (r1 : OrderCancelRejectOrderReplaceReject) :
    Message.decodeBytes (Message.encode (.orderCancelRejectOrderReplaceReject header r0 r1)) = some (.orderCancelRejectOrderReplaceReject header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [52, 51, 52] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ OrderCancelReject.tags ++ [[[52, 51, 52]]] ++ OrderCancelRejectOrderReplaceReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRejectOrderReplaceReject header r0 r1

theorem Message.decodeBytes_orderMassCancelReportAccepted (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportAccepted) :
    Message.decodeBytes (Message.encode (.orderMassCancelReportAccepted header r0 r1)) = some (.orderMassCancelReportAccepted header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[114], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 48], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportAccepted.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReportAccepted header r0 r1

theorem Message.decodeBytes_orderMassCancelReportRejected (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportRejected) :
    Message.decodeBytes (Message.encode (.orderMassCancelReportRejected header r0 r1)) = some (.orderMassCancelReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[114], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReportRejected header r0 r1

theorem Message.decodeBytes_orderMassCancelReportComplete (header : Header) (r0 : OrderMassCancelReport) (r1 : OrderMassCancelReportComplete) :
    Message.decodeBytes (Message.encode (.orderMassCancelReportComplete header r0 r1)) = some (.orderMassCancelReportComplete header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[114], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [53, 51, 49] ⟨[49, 48, 49], by decide⟩] ++ r1.parts) (Header.tags ++ OrderMassCancelReport.tags ++ [[[53, 51, 49]]] ++ OrderMassCancelReportComplete.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReportComplete header r0 r1

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decodeBytes_executionReportTrade header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | orderCancelRejectOrderCancelReject header r0 r1 => exact Message.decodeBytes_orderCancelRejectOrderCancelReject header r0 r1
  | orderCancelRejectOrderReplaceReject header r0 r1 => exact Message.decodeBytes_orderCancelRejectOrderReplaceReject header r0 r1
  | orderMassCancelReportAccepted header r0 r1 => exact Message.decodeBytes_orderMassCancelReportAccepted header r0 r1
  | orderMassCancelReportRejected header r0 r1 => exact Message.decodeBytes_orderMassCancelReportRejected header r0 r1
  | orderMassCancelReportComplete header r0 r1 => exact Message.decodeBytes_orderMassCancelReportComplete header r0 r1

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.TxseTxseequitiesOrderentryFixV028Exchange
