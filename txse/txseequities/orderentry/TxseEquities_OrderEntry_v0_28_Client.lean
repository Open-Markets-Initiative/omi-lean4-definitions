import Wire

/-!
# Texas Stock Exchange Order Entry v0.28, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.TxseTxseequitiesOrderentryFixV028Client

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

structure NewOrderSingle where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  symbol : Terminated 1  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  side : Terminated 1  -- tag 54
  locateReqd : Option (Terminated 1)  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  orderQty : Terminated 1  -- tag 38
  timeInForce : Terminated 1  -- tag 59
  orderCapacity : Terminated 1  -- tag 528
  clientID : Option (Terminated 1)  -- tag 109
  memberGroup : Option (Terminated 1)  -- tag 9004
  selfMatchScope : Option (Terminated 1)  -- tag 8001
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 2964
  userData : Option (Terminated 1)  -- tag 9002

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [53, 52] record.side,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.required [51, 56] record.orderQty,
   Part.required [53, 57] record.timeInForce,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 48, 48, 52] record.memberGroup,
   Part.optional [56, 48, 48, 49] record.selfMatchScope,
   Part.optional [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.optional [57, 48, 48, 50] record.userData]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[53, 53]], [[54, 53]], [[53, 52]], [[49, 49, 52]], [[57, 48, 48, 48]], [[51, 56]], [[53, 57]], [[53, 50, 56]], [[49, 48, 57]], [[57, 48, 48, 52]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[57, 48, 48, 50]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let side ← readRequired [53, 52] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let memberGroup ← readOptional [57, 48, 48, 52] tokens
  let selfMatchScope ← readOptional [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readOptional [50, 57, 54, 52] tokens
  let userData ← readOptional [57, 48, 48, 50] tokens
  pure { transactTime, clOrdID, symbol, symbolSfx, side, locateReqd, locateBroker, orderQty, timeInForce, orderCapacity, clientID, memberGroup, selfMatchScope, selfMatchPreventionInstruction, userData }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have memberGroup := readOptional_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have selfMatchScope := readOptional_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have userData := readOptional_part [57, 48, 48, 50] record.userData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [NewOrderSingle.decode, transactTime, clOrdID, symbol, symbolSfx, side, locateReqd, locateBroker, orderQty, timeInForce, orderCapacity, clientID, memberGroup, selfMatchScope, selfMatchPreventionInstruction, userData, some_bind] <;> rfl

structure NewOrderSingleNewLimitOrderSingle where
  price : Terminated 1  -- tag 44
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Option (Terminated 1)  -- tag 9005
  priceSlideInstruction : Option (Terminated 1)  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  minQty : Option (Terminated 1)  -- tag 110
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMinIncr : Option (Terminated 1)  -- tag 1087
  maxReplenishTimeRange : Option (Terminated 1)  -- tag 9001
  expireTime : Option (Terminated 1)  -- tag 126

def NewOrderSingleNewLimitOrderSingle.parts (record : NewOrderSingleNewLimitOrderSingle) : List Part :=
  [Part.required [52, 52] record.price,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.optional [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 55] record.displayMinIncr,
   Part.optional [57, 48, 48, 49] record.maxReplenishTimeRange,
   Part.optional [49, 50, 54] record.expireTime]

def NewOrderSingleNewLimitOrderSingle.tags : List (List (List UInt8)) :=
  [[[52, 52]], [[49, 56]], [[57, 48, 48, 53]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 48]], [[49, 49, 51, 56]], [[49, 48, 56, 55]], [[57, 48, 48, 49]], [[49, 50, 54]]]

theorem NewOrderSingleNewLimitOrderSingle.shape (record : NewOrderSingleNewLimitOrderSingle) : record.parts.map Part.tags = NewOrderSingleNewLimitOrderSingle.tags := rfl

def NewOrderSingleNewLimitOrderSingle.decode (tokens : List Token) : Option NewOrderSingleNewLimitOrderSingle := do
  let price ← readRequired [52, 52] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readOptional [57, 48, 48, 53] tokens
  let priceSlideInstruction ← readOptional [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMinIncr ← readOptional [49, 48, 56, 55] tokens
  let maxReplenishTimeRange ← readOptional [57, 48, 48, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  pure { price, execInst, cancelAtEntryIfCrossed, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime }

theorem NewOrderSingleNewLimitOrderSingle.decode_agrees (record : NewOrderSingleNewLimitOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingleNewLimitOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingleNewLimitOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingleNewLimitOrderSingle.tags.flatten.Nodup := by decide +kernel
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readOptional_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have priceSlideInstruction := readOptional_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have displayMinIncr := readOptional_part [49, 48, 56, 55] record.displayMinIncr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maxReplenishTimeRange := readOptional_part [57, 48, 48, 49] record.maxReplenishTimeRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NewOrderSingleNewLimitOrderSingle.decode, price, execInst, cancelAtEntryIfCrossed, priceSlideInstruction, pegOffsetValue, minQty, displayQty, displayMinIncr, maxReplenishTimeRange, expireTime, some_bind] <;> rfl

structure NewOrderSingleNewMarketOrderSingle

def NewOrderSingleNewMarketOrderSingle.parts (_ : NewOrderSingleNewMarketOrderSingle) : List Part :=
  []

def NewOrderSingleNewMarketOrderSingle.tags : List (List (List UInt8)) :=
  []

theorem NewOrderSingleNewMarketOrderSingle.shape (record : NewOrderSingleNewMarketOrderSingle) : record.parts.map Part.tags = NewOrderSingleNewMarketOrderSingle.tags := rfl

def NewOrderSingleNewMarketOrderSingle.decode (_ : List Token) : Option NewOrderSingleNewMarketOrderSingle := some {}

theorem NewOrderSingleNewMarketOrderSingle.decode_agrees (record : NewOrderSingleNewMarketOrderSingle) (tokens : List Token)
    (_ : ∀ tags ∈ NewOrderSingleNewMarketOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingleNewMarketOrderSingle.decode tokens = some record := by
  rfl

structure OrderCancelRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  side : Terminated 1  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [53, 52] record.side,
   Part.optional [51, 56] record.orderQty]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[52, 49]], [[53, 53]], [[54, 53]], [[53, 52]], [[51, 56]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  pure { transactTime, clOrdID, origClOrdID, symbol, symbolSfx, side, orderQty }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, transactTime, clOrdID, origClOrdID, symbol, symbolSfx, side, orderQty, some_bind] <;> rfl

structure OrderReplaceRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  side : Terminated 1  -- tag 54
  ordType : Option (Terminated 1)  -- tag 40
  locateReqd : Option (Terminated 1)  -- tag 114
  locateBroker : Option (Terminated 1)  -- tag 9000
  price : Option (Terminated 1)  -- tag 44
  orderQty : Option (Terminated 1)  -- tag 38
  execInst : Option (Terminated 1)  -- tag 18
  cancelAtEntryIfCrossed : Option (Terminated 1)  -- tag 9005
  selfMatchScope : Option (Terminated 1)  -- tag 8001
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 2964
  priceSlideInstruction : Option (Terminated 1)  -- tag 8000
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  displayQty : Option (Terminated 1)  -- tag 1138

def OrderReplaceRequest.parts (record : OrderReplaceRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [53, 52] record.side,
   Part.optional [52, 48] record.ordType,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [57, 48, 48, 48] record.locateBroker,
   Part.optional [52, 52] record.price,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 48, 48, 53] record.cancelAtEntryIfCrossed,
   Part.optional [56, 48, 48, 49] record.selfMatchScope,
   Part.optional [50, 57, 54, 52] record.selfMatchPreventionInstruction,
   Part.optional [56, 48, 48, 48] record.priceSlideInstruction,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 49, 51, 56] record.displayQty]

def OrderReplaceRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[52, 49]], [[53, 53]], [[54, 53]], [[53, 52]], [[52, 48]], [[49, 49, 52]], [[57, 48, 48, 48]], [[52, 52]], [[51, 56]], [[49, 56]], [[57, 48, 48, 53]], [[56, 48, 48, 49]], [[50, 57, 54, 52]], [[56, 48, 48, 48]], [[50, 49, 49]], [[49, 49, 51, 56]]]

theorem OrderReplaceRequest.shape (record : OrderReplaceRequest) : record.parts.map Part.tags = OrderReplaceRequest.tags := rfl

def OrderReplaceRequest.decode (tokens : List Token) : Option OrderReplaceRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let side ← readRequired [53, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let locateBroker ← readOptional [57, 48, 48, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let execInst ← readOptional [49, 56] tokens
  let cancelAtEntryIfCrossed ← readOptional [57, 48, 48, 53] tokens
  let selfMatchScope ← readOptional [56, 48, 48, 49] tokens
  let selfMatchPreventionInstruction ← readOptional [50, 57, 54, 52] tokens
  let priceSlideInstruction ← readOptional [56, 48, 48, 48] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  pure { transactTime, clOrdID, origClOrdID, symbol, symbolSfx, side, ordType, locateReqd, locateBroker, price, orderQty, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty }

theorem OrderReplaceRequest.decode_agrees (record : OrderReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderReplaceRequest.decode tokens = some record := by
  have distinct : OrderReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have locateBroker := readOptional_part [57, 48, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have cancelAtEntryIfCrossed := readOptional_part [57, 48, 48, 53] record.cancelAtEntryIfCrossed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have selfMatchScope := readOptional_part [56, 48, 48, 49] record.selfMatchScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [50, 57, 54, 52] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have priceSlideInstruction := readOptional_part [56, 48, 48, 48] record.priceSlideInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [OrderReplaceRequest.decode, transactTime, clOrdID, origClOrdID, symbol, symbolSfx, side, ordType, locateReqd, locateBroker, price, orderQty, execInst, cancelAtEntryIfCrossed, selfMatchScope, selfMatchPreventionInstruction, priceSlideInstruction, pegOffsetValue, displayQty, some_bind] <;> rfl

structure OrderMassCancelRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  clientID : Option (Terminated 1)  -- tag 109
  refCompID : Option (Terminated 1)  -- tag 930
  memberGroup : Option (Terminated 1)  -- tag 9004
  origClOrdID : Option (Terminated 1)  -- tag 41
  excludeAuctionOrders : Option (Terminated 1)  -- tag 9009

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 51, 48] record.refCompID,
   Part.optional [57, 48, 48, 52] record.memberGroup,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [57, 48, 48, 57] record.excludeAuctionOrders]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[53, 51, 48]], [[49, 48, 57]], [[57, 51, 48]], [[57, 48, 48, 52]], [[52, 49]], [[57, 48, 48, 57]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let refCompID ← readOptional [57, 51, 48] tokens
  let memberGroup ← readOptional [57, 48, 48, 52] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let excludeAuctionOrders ← readOptional [57, 48, 48, 57] tokens
  pure { transactTime, clOrdID, massCancelRequestType, clientID, refCompID, memberGroup, origClOrdID, excludeAuctionOrders }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have refCompID := readOptional_part [57, 51, 48] record.refCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have memberGroup := readOptional_part [57, 48, 48, 52] record.memberGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have excludeAuctionOrders := readOptional_part [57, 48, 48, 57] record.excludeAuctionOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, transactTime, clOrdID, massCancelRequestType, clientID, refCompID, memberGroup, origClOrdID, excludeAuctionOrders, some_bind] <;> rfl

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | newOrderSingleNewLimitOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewLimitOrderSingle)
  | newOrderSingleNewMarketOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewMarketOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderReplaceRequest (header : Header) (r0 : OrderReplaceRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingleNewLimitOrderSingle header r0 r1 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .newOrderSingleNewMarketOrderSingle header r0 r1 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], ⟨[113], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [68] then
        match readRequired [52, 48] rest with
        | none => none
        | some key =>
          if key.val = [50] then
            if known (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewLimitOrderSingle.tags) rest then do
              let header ← Header.decode rest
              let r0 ← NewOrderSingle.decode rest
              let r1 ← NewOrderSingleNewLimitOrderSingle.decode rest
              pure (.newOrderSingleNewLimitOrderSingle header r0 r1)
            else none
          else if key.val = [49] then
            if known (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewMarketOrderSingle.tags) rest then do
              let header ← Header.decode rest
              let r0 ← NewOrderSingle.decode rest
              let r1 ← NewOrderSingleNewMarketOrderSingle.decode rest
              pure (.newOrderSingleNewMarketOrderSingle header r0 r1)
            else none
          else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderReplaceRequest.decode rest
          pure (.orderReplaceRequest header r0)
        else none
      else if token.value.val = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
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

theorem Message.decode_newOrderSingleNewLimitOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewLimitOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingleNewLimitOrderSingle header r0 r1)) = some (.newOrderSingleNewLimitOrderSingle header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [52, 48] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewLimitOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [52, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (NewOrderSingle.tags) ([[[52, 48]]] ++ NewOrderSingleNewLimitOrderSingle.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [52, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [52, 48] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ NewOrderSingle.tags) ([[[52, 48]]]) (NewOrderSingleNewLimitOrderSingle.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := NewOrderSingleNewLimitOrderSingle.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]]) (NewOrderSingleNewLimitOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewLimitOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingleNewMarketOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewMarketOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingleNewMarketOrderSingle header r0 r1)) = some (.newOrderSingleNewMarketOrderSingle header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [52, 48] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewMarketOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [52, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (NewOrderSingle.tags) ([[[52, 48]]] ++ NewOrderSingleNewMarketOrderSingle.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [52, 48] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [52, 48] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ NewOrderSingle.tags) ([[[52, 48]]]) (NewOrderSingleNewMarketOrderSingle.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := NewOrderSingleNewMarketOrderSingle.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]]) (NewOrderSingleNewMarketOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewMarketOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderReplaceRequest (header : Header) (r0 : OrderReplaceRequest) :
    Message.decode (Message.tokens (.orderReplaceRequest header r0)) = some (.orderReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | newOrderSingleNewLimitOrderSingle header r0 r1 => exact Message.decode_newOrderSingleNewLimitOrderSingle header r0 r1
  | newOrderSingleNewMarketOrderSingle header r0 r1 => exact Message.decode_newOrderSingleNewMarketOrderSingle header r0 r1
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderReplaceRequest header r0 => exact Message.decode_orderReplaceRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0

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

theorem Message.decodeBytes_newOrderSingleNewLimitOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewLimitOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingleNewLimitOrderSingle header r0 r1)) = some (.newOrderSingleNewLimitOrderSingle header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewLimitOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingleNewLimitOrderSingle header r0 r1

theorem Message.decodeBytes_newOrderSingleNewMarketOrderSingle (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleNewMarketOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingleNewMarketOrderSingle header r0 r1)) = some (.newOrderSingleNewMarketOrderSingle header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [52, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[52, 48]]] ++ NewOrderSingleNewMarketOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingleNewMarketOrderSingle header r0 r1

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderReplaceRequest (header : Header) (r0 : OrderReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderReplaceRequest header r0)) = some (.orderReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderReplaceRequest header r0

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[113], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | newOrderSingleNewLimitOrderSingle header r0 r1 => exact Message.decodeBytes_newOrderSingleNewLimitOrderSingle header r0 r1
  | newOrderSingleNewMarketOrderSingle header r0 r1 => exact Message.decodeBytes_newOrderSingleNewMarketOrderSingle header r0 r1
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderReplaceRequest header r0 => exact Message.decodeBytes_orderReplaceRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.TxseTxseequitiesOrderentryFixV028Client
