import Wire

/-!
# Box Options Market Order Entry v4.8, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.BoxBoxoptionsOrderentryFixV48Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  origSendingTime : Option (Terminated 1)  -- tag 122
  possResend : Option (Terminated 1)  -- tag 97

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [57, 55] record.possResend]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[49, 50, 50]], [[57, 55]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let possResend ← readOptional [57, 55] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, origSendingTime, possResend }

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
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, origSendingTime, possResend, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  maxMessageSize : Option (Terminated 1)  -- tag 383

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [51, 56, 51] record.maxMessageSize]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[51, 56, 51]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let maxMessageSize ← readOptional [51, 56, 51] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, maxMessageSize }

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
  have maxMessageSize := readOptional_part [51, 56, 51] record.maxMessageSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, maxMessageSize, some_bind] <;> rfl

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

structure FIXProtocolErrorReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def FIXProtocolErrorReject.parts (record : FIXProtocolErrorReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def FIXProtocolErrorReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem FIXProtocolErrorReject.shape (record : FIXProtocolErrorReject) : record.parts.map Part.tags = FIXProtocolErrorReject.tags := rfl

def FIXProtocolErrorReject.decode (tokens : List Token) : Option FIXProtocolErrorReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refTagID, refMsgType, sessionRejectReason, text }

theorem FIXProtocolErrorReject.decode_agrees (record : FIXProtocolErrorReject) (tokens : List Token)
    (agrees : ∀ tags ∈ FIXProtocolErrorReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    FIXProtocolErrorReject.decode tokens = some record := by
  have distinct : FIXProtocolErrorReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [FIXProtocolErrorReject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

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

structure ExecutionReport where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  execInst : Option (Terminated 1)  -- tag 18
  account : Option (Terminated 1)  -- tag 1
  execID : Option (Terminated 1)  -- tag 17
  execTransType : Option (Terminated 1)  -- tag 20
  execRefID : Option (Terminated 1)  -- tag 19
  execType : Option (Terminated 1)  -- tag 150
  ordRejReason : Option (Terminated 1)  -- tag 103
  ordStatus : Option (Terminated 1)  -- tag 39
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  securityType : Option (Terminated 1)  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  side : Option (Terminated 1)  -- tag 54
  ordType : Option (Terminated 1)  -- tag 40
  timeInForce : Option (Terminated 1)  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  lastShares : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Option (Terminated 1)  -- tag 151
  cumQty : Option (Terminated 1)  -- tag 14
  avgPx : Option (Terminated 1)  -- tag 6
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Option (Terminated 1)  -- tag 77
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  clearingFirm : Option (Terminated 1)  -- tag 439
  rule80A : Option (Terminated 1)  -- tag 47
  multiLegReportingType : Option (Terminated 1)  -- tag 442
  noContraBrokers : Option (Terminated 1)  -- tag 382
  contraBroker : Option (Terminated 1)  -- tag 375
  massStatusReqID2 : Option (Terminated 1)  -- tag 584
  trdType : Option (Terminated 1)  -- tag 828
  improvePhaseID : Option (Terminated 1)  -- tag 7900
  combinedOrdType : Option (Terminated 1)  -- tag 7906
  auctionType : Option (Terminated 1)  -- tag 9383
  contingentOrder : Option (Terminated 1)  -- tag 7388
  specialTradeInd : Option (Terminated 1)  -- tag 9459
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  addQty : Option (Terminated 1)  -- tag 9461
  qtyType : Option (Terminated 1)  -- tag 854
  priceImprovement : Option (Terminated 1)  -- tag 639
  legRefID : Option (Terminated 1)  -- tag 654
  securityAltId : Option (Terminated 1)  -- tag 10455
  secondaryExedId : Option (Terminated 1)  -- tag 527
  contraAccountType : Option (Terminated 1)  -- tag 6005

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49] record.account,
   Part.optional [49, 55] record.execID,
   Part.optional [50, 48] record.execTransType,
   Part.optional [49, 57] record.execRefID,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [53, 52] record.side,
   Part.optional [52, 48] record.ordType,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 49] record.lastPx,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 52] record.cumQty,
   Part.optional [54] record.avgPx,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 55] record.openClose,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 55] record.rule80A,
   Part.optional [52, 52, 50] record.multiLegReportingType,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [53, 56, 52] record.massStatusReqID2,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [55, 57, 48, 48] record.improvePhaseID,
   Part.optional [55, 57, 48, 54] record.combinedOrdType,
   Part.optional [57, 51, 56, 51] record.auctionType,
   Part.optional [55, 51, 56, 56] record.contingentOrder,
   Part.optional [57, 52, 53, 57] record.specialTradeInd,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [57, 52, 54, 49] record.addQty,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [54, 51, 57] record.priceImprovement,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [49, 48, 52, 53, 53] record.securityAltId,
   Part.optional [53, 50, 55] record.secondaryExedId,
   Part.optional [54, 48, 48, 53] record.contraAccountType]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[49, 56]], [[49]], [[49, 55]], [[50, 48]], [[49, 57]], [[49, 53, 48]], [[49, 48, 51]], [[51, 57]], [[51, 56]], [[52, 52]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52]], [[52, 48]], [[53, 57]], [[52, 51, 50]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[54]], [[54, 48]], [[55, 55]], [[53, 56]], [[55, 54]], [[52, 51, 57]], [[52, 55]], [[52, 52, 50]], [[51, 56, 50]], [[51, 55, 53]], [[53, 56, 52]], [[56, 50, 56]], [[55, 57, 48, 48]], [[55, 57, 48, 54]], [[57, 51, 56, 51]], [[55, 51, 56, 56]], [[57, 52, 53, 57]], [[57, 55, 51, 48]], [[57, 52, 54, 49]], [[56, 53, 52]], [[54, 51, 57]], [[54, 53, 52]], [[49, 48, 52, 53, 53]], [[53, 50, 55]], [[54, 48, 48, 53]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let account ← readOptional [49] tokens
  let execID ← readOptional [49, 55] tokens
  let execTransType ← readOptional [50, 48] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let side ← readOptional [53, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let lastShares ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let avgPx ← readOptional [54] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let multiLegReportingType ← readOptional [52, 52, 50] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let massStatusReqID2 ← readOptional [53, 56, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let improvePhaseID ← readOptional [55, 57, 48, 48] tokens
  let combinedOrdType ← readOptional [55, 57, 48, 54] tokens
  let auctionType ← readOptional [57, 51, 56, 51] tokens
  let contingentOrder ← readOptional [55, 51, 56, 56] tokens
  let specialTradeInd ← readOptional [57, 52, 53, 57] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let addQty ← readOptional [57, 52, 54, 49] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let priceImprovement ← readOptional [54, 51, 57] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let securityAltId ← readOptional [49, 48, 52, 53, 53] tokens
  let secondaryExedId ← readOptional [53, 50, 55] tokens
  let contraAccountType ← readOptional [54, 48, 48, 53] tokens
  pure { orderID, clOrdID, origClOrdID, execInst, account, execID, execTransType, execRefID, execType, ordRejReason, ordStatus, orderQty, price, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, ordType, timeInForce, expireDate, lastShares, lastPx, leavesQty, cumQty, avgPx, transactTime, openClose, text, execBroker, clearingFirm, rule80A, multiLegReportingType, noContraBrokers, contraBroker, massStatusReqID2, trdType, improvePhaseID, combinedOrdType, auctionType, contingentOrder, specialTradeInd, tradeLiquidityIndicator, addQty, qtyType, priceImprovement, legRefID, securityAltId, secondaryExedId, contraAccountType }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have multiLegReportingType := readOptional_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have massStatusReqID2 := readOptional_part [53, 56, 52] record.massStatusReqID2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have improvePhaseID := readOptional_part [55, 57, 48, 48] record.improvePhaseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have combinedOrdType := readOptional_part [55, 57, 48, 54] record.combinedOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 56, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have contingentOrder := readOptional_part [55, 51, 56, 56] record.contingentOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have specialTradeInd := readOptional_part [57, 52, 53, 57] record.specialTradeInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have addQty := readOptional_part [57, 52, 54, 49] record.addQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have priceImprovement := readOptional_part [54, 51, 57] record.priceImprovement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have securityAltId := readOptional_part [49, 48, 52, 53, 53] record.securityAltId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have secondaryExedId := readOptional_part [53, 50, 55] record.secondaryExedId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have contraAccountType := readOptional_part [54, 48, 48, 53] record.contraAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, origClOrdID, execInst, account, execID, execTransType, execRefID, execType, ordRejReason, ordStatus, orderQty, price, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, ordType, timeInForce, expireDate, lastShares, lastPx, leavesQty, cumQty, avgPx, transactTime, openClose, text, execBroker, clearingFirm, rule80A, multiLegReportingType, noContraBrokers, contraBroker, massStatusReqID2, trdType, improvePhaseID, combinedOrdType, auctionType, contingentOrder, specialTradeInd, tradeLiquidityIndicator, addQty, qtyType, priceImprovement, legRefID, securityAltId, secondaryExedId, contraAccountType, some_bind] <;> rfl

structure OrderSingleComplexCancelReject where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  ordStatus : Option (Terminated 1)  -- tag 39
  cxlRejResponseTo : Option (Terminated 1)  -- tag 434
  text : Option (Terminated 1)  -- tag 58

def OrderSingleComplexCancelReject.parts (record : OrderSingleComplexCancelReject) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [53, 56] record.text]

def OrderSingleComplexCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[52, 51, 52]], [[53, 56]]]

theorem OrderSingleComplexCancelReject.shape (record : OrderSingleComplexCancelReject) : record.parts.map Part.tags = OrderSingleComplexCancelReject.tags := rfl

def OrderSingleComplexCancelReject.decode (tokens : List Token) : Option OrderSingleComplexCancelReject := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let cxlRejResponseTo ← readOptional [52, 51, 52] tokens
  let text ← readOptional [53, 56] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, text }

theorem OrderSingleComplexCancelReject.decode_agrees (record : OrderSingleComplexCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderSingleComplexCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderSingleComplexCancelReject.decode tokens = some record := by
  have distinct : OrderSingleComplexCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cxlRejResponseTo := readOptional_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderSingleComplexCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, text, some_bind] <;> rfl

structure QuoteAcknowledgement where
  quoteReqID : Option (Terminated 1)  -- tag 131
  quoteAckStatus : Option (Terminated 1)  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300

def QuoteAcknowledgement.parts (record : QuoteAcknowledgement) : List Part :=
  [Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [50, 57, 55] record.quoteAckStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason]

def QuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[50, 57, 55]], [[51, 48, 48]]]

theorem QuoteAcknowledgement.shape (record : QuoteAcknowledgement) : record.parts.map Part.tags = QuoteAcknowledgement.tags := rfl

def QuoteAcknowledgement.decode (tokens : List Token) : Option QuoteAcknowledgement := do
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let quoteAckStatus ← readOptional [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  pure { quoteReqID, quoteAckStatus, quoteRejectReason }

theorem QuoteAcknowledgement.decode_agrees (record : QuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteAcknowledgement.decode tokens = some record := by
  have distinct : QuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteAckStatus := readOptional_part [50, 57, 55] record.quoteAckStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [QuoteAcknowledgement.decode, quoteReqID, quoteAckStatus, quoteRejectReason, some_bind] <;> rfl

structure SecurityDefinition where
  securityReqID : Option (Terminated 1)  -- tag 320
  securityResponseID : Option (Terminated 1)  -- tag 322
  securityResponseType : Option (Terminated 1)  -- tag 323
  symbol : Option (Terminated 1)  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  noRelatedSym : Option (Terminated 1)  -- tag 146

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.optional [51, 50, 48] record.securityReqID,
   Part.optional [51, 50, 50] record.securityResponseID,
   Part.optional [51, 50, 51] record.securityResponseType,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [49, 52, 54] record.noRelatedSym]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 50]], [[51, 50, 51]], [[53, 53]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[52, 56]], [[50, 50]], [[49, 52, 54]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readOptional [51, 50, 48] tokens
  let securityResponseID ← readOptional [51, 50, 50] tokens
  let securityResponseType ← readOptional [51, 50, 51] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let noRelatedSym ← readOptional [49, 52, 54] tokens
  pure { securityReqID, securityResponseID, securityResponseType, symbol, securityType, maturityMonthYear, maturityDay, putOrCall, strikePrice, securityID, iDSource, noRelatedSym }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readOptional_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseID := readOptional_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityResponseType := readOptional_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noRelatedSym := readOptional_part [49, 52, 54] record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseID, securityResponseType, symbol, securityType, maturityMonthYear, maturityDay, putOrCall, strikePrice, securityID, iDSource, noRelatedSym, some_bind] <;> rfl

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  refMsgType : Option (Terminated 1)  -- tag 372
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Option (Terminated 1)  -- tag 380
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.optional [51, 56, 48] record.businessRejectReason,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 57]], [[51, 56, 48]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readOptional [51, 56, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, businessRejectRefID, businessRejectReason, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectReason := readOptional_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, businessRejectRefID, businessRejectReason, text, some_bind] <;> rfl

structure UserResponse where
  transactTime : Option (Terminated 1)  -- tag 60
  userRequestId : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924
  securityType : Option (Terminated 1)  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  strikePrice : Option (Terminated 1)  -- tag 202
  rule80A : Option (Terminated 1)  -- tag 47

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.optional [54, 48] record.transactTime,
   Part.required [57, 50, 51] record.userRequestId,
   Part.required [57, 50, 52] record.userRequestType,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [52, 55] record.rule80A]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[57, 50, 51]], [[57, 50, 52]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 50]], [[52, 55]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let transactTime ← readOptional [54, 48] tokens
  let userRequestId ← readRequired [57, 50, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let rule80A ← readOptional [52, 55] tokens
  pure { transactTime, userRequestId, userRequestType, securityType, symbol, putOrCall, maturityMonthYear, maturityDay, strikePrice, rule80A }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userRequestId := readRequired_part [57, 50, 51] record.userRequestId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [UserResponse.decode, transactTime, userRequestId, userRequestType, securityType, symbol, putOrCall, maturityMonthYear, maturityDay, strikePrice, rule80A, some_bind] <;> rfl

structure UserNotification where
  transactTime : Option (Terminated 1)  -- tag 60
  userStatus : Option (Terminated 1)  -- tag 926
  riskTeamStatus : Option (Terminated 1)  -- tag 7926

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.optional [54, 48] record.transactTime,
   Part.optional [57, 50, 54] record.userStatus,
   Part.optional [55, 57, 50, 54] record.riskTeamStatus]

def UserNotification.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[57, 50, 54]], [[55, 57, 50, 54]]]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let transactTime ← readOptional [54, 48] tokens
  let userStatus ← readOptional [57, 50, 54] tokens
  let riskTeamStatus ← readOptional [55, 57, 50, 54] tokens
  pure { transactTime, userStatus, riskTeamStatus }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userStatus := readOptional_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have riskTeamStatus := readOptional_part [55, 57, 50, 54] record.riskTeamStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [UserNotification.decode, transactTime, userStatus, riskTeamStatus, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | fIXProtocolErrorReject (header : Header) (r0 : FIXProtocolErrorReject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderSingleComplexCancelReject (header : Header) (r0 : OrderSingleComplexCancelReject)
  | quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | userResponse (header : Header) (r0 : UserResponse)
  | userNotification (header : Header) (r0 : UserNotification)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .fIXProtocolErrorReject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderSingleComplexCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteAcknowledgement header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userNotification header r0 => ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
        if known (Header.tags ++ FIXProtocolErrorReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← FIXProtocolErrorReject.decode rest
          pure (.fIXProtocolErrorReject header r0)
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
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderSingleComplexCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderSingleComplexCancelReject.decode rest
          pure (.orderSingleComplexCancelReject header r0)
        else none
      else if token.value.val = [98] then
        if known (Header.tags ++ QuoteAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteAcknowledgement.decode rest
          pure (.quoteAcknowledgement header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else if token.value.val = [67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
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

theorem Message.decode_fIXProtocolErrorReject (header : Header) (r0 : FIXProtocolErrorReject) :
    Message.decode (Message.tokens (.fIXProtocolErrorReject header r0)) = some (.fIXProtocolErrorReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (FIXProtocolErrorReject.tags) rfl rfl (by decide +kernel))
  have c1 := FIXProtocolErrorReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (FIXProtocolErrorReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ FIXProtocolErrorReject.tags) rfl
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

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderSingleComplexCancelReject (header : Header) (r0 : OrderSingleComplexCancelReject) :
    Message.decode (Message.tokens (.orderSingleComplexCancelReject header r0)) = some (.orderSingleComplexCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderSingleComplexCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderSingleComplexCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderSingleComplexCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderSingleComplexCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement) :
    Message.decode (Message.tokens (.quoteAcknowledgement header r0)) = some (.quoteAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
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

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | fIXProtocolErrorReject header r0 => exact Message.decode_fIXProtocolErrorReject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderSingleComplexCancelReject header r0 => exact Message.decode_orderSingleComplexCancelReject header r0
  | quoteAcknowledgement header r0 => exact Message.decode_quoteAcknowledgement header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0
  | userNotification header r0 => exact Message.decode_userNotification header r0

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

theorem Message.decodeBytes_fIXProtocolErrorReject (header : Header) (r0 : FIXProtocolErrorReject) :
    Message.decodeBytes (Message.encode (.fIXProtocolErrorReject header r0)) = some (.fIXProtocolErrorReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ FIXProtocolErrorReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_fIXProtocolErrorReject header r0

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

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_orderSingleComplexCancelReject (header : Header) (r0 : OrderSingleComplexCancelReject) :
    Message.decodeBytes (Message.encode (.orderSingleComplexCancelReject header r0)) = some (.orderSingleComplexCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderSingleComplexCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderSingleComplexCancelReject header r0

theorem Message.decodeBytes_quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement) :
    Message.decodeBytes (Message.encode (.quoteAcknowledgement header r0)) = some (.quoteAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[98], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteAcknowledgement header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | fIXProtocolErrorReject header r0 => exact Message.decodeBytes_fIXProtocolErrorReject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderSingleComplexCancelReject header r0 => exact Message.decodeBytes_orderSingleComplexCancelReject header r0
  | quoteAcknowledgement header r0 => exact Message.decodeBytes_quoteAcknowledgement header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.BoxBoxoptionsOrderentryFixV48Exchange
