import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v2026.1, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNsmequitiesTradereportingFixV20261Exchange

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  secureDataLen : Option (Terminated 1)  -- tag 90
  secureData : Option (Terminated 1)  -- tag 91
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.optional [57, 48] record.secureDataLen,
   Part.optional [57, 49] record.secureData,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 48]], [[57, 49]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let secureDataLen ← readOptional [57, 48] tokens
  let secureData ← readOptional [57, 49] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, secureDataLen, secureData, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime }

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
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have secureDataLen := readOptional_part [57, 48] record.secureDataLen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have secureData := readOptional_part [57, 49] record.secureData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, secureDataLen, secureData, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 48] record.secureDataLen (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 49] record.secureData (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
               (paired_none pairing)))))))))))))

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

structure Logon where
  rawData : Option (List UInt8)  -- tag 96
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108

def Logon.parts (record : Logon) : List Part :=
  [Part.dataOptional [57, 53] [57, 54] record.rawData,
   Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 53], [57, 54]], [[57, 56]], [[49, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  pure { rawData, encryptMethod, heartBtInt }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have rawData := readDataOptional_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Logon.decode, rawData, encryptMethod, heartBtInt, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
     (paired_none pairing)))

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

structure SequenceReset where
  newSeqNum : Terminated 1  -- tag 36
  gapFillFlag : Option (Terminated 1)  -- tag 123

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [51, 54] record.newSeqNum,
   Part.optional [49, 50, 51] record.gapFillFlag]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[51, 54]], [[49, 50, 51]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let newSeqNum ← readRequired [51, 54] tokens
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  pure { newSeqNum, gapFillFlag }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have newSeqNum := readRequired_part [51, 54] record.newSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, newSeqNum, gapFillFlag, some_bind] <;> rfl

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagId : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagId,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagId ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  pure { refSeqNum, text, refTagId, refMsgType, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagId := readOptional_part [51, 55, 49] record.refTagId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagId, refMsgType, sessionRejectReason, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagId (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
       (paired_none pairing)))))

structure TradeCaptureReport where
  avgPx : Terminated 1  -- tag 6
  clOrdID : Option (Terminated 1)  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  tradeDate : Option (Terminated 1)  -- tag 75
  processCode : Option (Terminated 1)  -- tag 81
  securityDesc : Option (Terminated 1)  -- tag 107
  leavesQty : Terminated 1  -- tag 151
  mDMkt : Option (Terminated 1)  -- tag 275
  tradeCondition : Option (Terminated 1)  -- tag 277
  contraBroker : Option (Terminated 1)  -- tag 375
  priceType : Option (Terminated 1)  -- tag 423
  clearingAccount : Option (Terminated 1)  -- tag 440
  secondaryExecId : Option (Terminated 1)  -- tag 527
  orderCapacity : Option (Terminated 1)  -- tag 528
  tradeReportID : Option (Terminated 1)  -- tag 571
  clearingInstruction : Option (Terminated 1)  -- tag 577
  reversalIndicator : Option (Terminated 1)  -- tag 700
  trdSubType : Terminated 1  -- tag 829
  publishTrdIndicator : Option (Terminated 1)  -- tag 852
  shortSaleReason : Option (Terminated 1)  -- tag 853
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  tradeReportType : Option (Terminated 1)  -- tag 856
  trdMatchID : Option (Terminated 1)  -- tag 880
  asOfIndicator : Option (Terminated 1)  -- tag 5080
  memo : Option (Terminated 1)  -- tag 5149
  relatedMarketCenter : Option (Terminated 1)  -- tag 9277
  advertisementInstruction : Option (Terminated 1)  -- tag 9278
  clearingPrice : Option (Terminated 1)  -- tag 9822
  reportingGUID : Option (Terminated 1)  -- tag 9825
  nonReportingGUID : Option (Terminated 1)  -- tag 9826
  overrideFlag : Option (Terminated 1)  -- tag 9854
  contraBranchSeqNbr : Option (Terminated 1)  -- tag 9860
  contraTradePA : Option (Terminated 1)  -- tag 9862
  contraClearingAcct : Option (Terminated 1)  -- tag 9863
  origControlDate : Option (Terminated 1)  -- tag 22012
  tradeModifier4Time : Option (Terminated 1)  -- tag 22018
  shortSaleIndicator : Option (Terminated 1)  -- tag 22024
  refReportingFacility : Option (Terminated 1)  -- tag 22029
  tradeModifier2Time : Option (Terminated 1)  -- tag 22033
  tradeReportRefID : Option (Terminated 1)  -- tag 572

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [54] record.avgPx,
   Part.optional [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [56, 49] record.processCode,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 55, 53] record.mDMkt,
   Part.optional [50, 55, 55] record.tradeCondition,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 55] record.secondaryExecId,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 55, 49] record.tradeReportID,
   Part.optional [53, 55, 55] record.clearingInstruction,
   Part.optional [55, 48, 48] record.reversalIndicator,
   Part.required [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 50] record.publishTrdIndicator,
   Part.optional [56, 53, 51] record.shortSaleReason,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [53, 48, 56, 48] record.asOfIndicator,
   Part.optional [53, 49, 52, 57] record.memo,
   Part.optional [57, 50, 55, 55] record.relatedMarketCenter,
   Part.optional [57, 50, 55, 56] record.advertisementInstruction,
   Part.optional [57, 56, 50, 50] record.clearingPrice,
   Part.optional [57, 56, 50, 53] record.reportingGUID,
   Part.optional [57, 56, 50, 54] record.nonReportingGUID,
   Part.optional [57, 56, 53, 52] record.overrideFlag,
   Part.optional [57, 56, 54, 48] record.contraBranchSeqNbr,
   Part.optional [57, 56, 54, 50] record.contraTradePA,
   Part.optional [57, 56, 54, 51] record.contraClearingAcct,
   Part.optional [50, 50, 48, 49, 50] record.origControlDate,
   Part.optional [50, 50, 48, 49, 56] record.tradeModifier4Time,
   Part.optional [50, 50, 48, 50, 52] record.shortSaleIndicator,
   Part.optional [50, 50, 48, 50, 57] record.refReportingFacility,
   Part.optional [50, 50, 48, 51, 51] record.tradeModifier2Time,
   Part.optional [53, 55, 50] record.tradeReportRefID]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 55]], [[51, 57]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[55, 53]], [[56, 49]], [[49, 48, 55]], [[49, 53, 49]], [[50, 55, 53]], [[50, 55, 55]], [[51, 55, 53]], [[52, 50, 51]], [[52, 52, 48]], [[53, 50, 55]], [[53, 50, 56]], [[53, 55, 49]], [[53, 55, 55]], [[55, 48, 48]], [[56, 50, 57]], [[56, 53, 50]], [[56, 53, 51]], [[56, 53, 53]], [[56, 53, 54]], [[56, 56, 48]], [[53, 48, 56, 48]], [[53, 49, 52, 57]], [[57, 50, 55, 55]], [[57, 50, 55, 56]], [[57, 56, 50, 50]], [[57, 56, 50, 53]], [[57, 56, 50, 54]], [[57, 56, 53, 52]], [[57, 56, 54, 48]], [[57, 56, 54, 50]], [[57, 56, 54, 51]], [[50, 50, 48, 49, 50]], [[50, 50, 48, 49, 56]], [[50, 50, 48, 50, 52]], [[50, 50, 48, 50, 57]], [[50, 50, 48, 51, 51]], [[53, 55, 50]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let processCode ← readOptional [56, 49] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let mDMkt ← readOptional [50, 55, 53] tokens
  let tradeCondition ← readOptional [50, 55, 55] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let secondaryExecId ← readOptional [53, 50, 55] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let tradeReportID ← readOptional [53, 55, 49] tokens
  let clearingInstruction ← readOptional [53, 55, 55] tokens
  let reversalIndicator ← readOptional [55, 48, 48] tokens
  let trdSubType ← readRequired [56, 50, 57] tokens
  let publishTrdIndicator ← readOptional [56, 53, 50] tokens
  let shortSaleReason ← readOptional [56, 53, 51] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let asOfIndicator ← readOptional [53, 48, 56, 48] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  let relatedMarketCenter ← readOptional [57, 50, 55, 55] tokens
  let advertisementInstruction ← readOptional [57, 50, 55, 56] tokens
  let clearingPrice ← readOptional [57, 56, 50, 50] tokens
  let reportingGUID ← readOptional [57, 56, 50, 53] tokens
  let nonReportingGUID ← readOptional [57, 56, 50, 54] tokens
  let overrideFlag ← readOptional [57, 56, 53, 52] tokens
  let contraBranchSeqNbr ← readOptional [57, 56, 54, 48] tokens
  let contraTradePA ← readOptional [57, 56, 54, 50] tokens
  let contraClearingAcct ← readOptional [57, 56, 54, 51] tokens
  let origControlDate ← readOptional [50, 50, 48, 49, 50] tokens
  let tradeModifier4Time ← readOptional [50, 50, 48, 49, 56] tokens
  let shortSaleIndicator ← readOptional [50, 50, 48, 50, 52] tokens
  let refReportingFacility ← readOptional [50, 50, 48, 50, 57] tokens
  let tradeModifier2Time ← readOptional [50, 50, 48, 51, 51] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  pure { avgPx, clOrdID, cumQty, execID, execTransType, orderID, ordStatus, side, symbol, transactTime, symbolSfx, tradeDate, processCode, securityDesc, leavesQty, mDMkt, tradeCondition, contraBroker, priceType, clearingAccount, secondaryExecId, orderCapacity, tradeReportID, clearingInstruction, reversalIndicator, trdSubType, publishTrdIndicator, shortSaleReason, secondaryTrdType, tradeReportType, trdMatchID, asOfIndicator, memo, relatedMarketCenter, advertisementInstruction, clearingPrice, reportingGUID, nonReportingGUID, overrideFlag, contraBranchSeqNbr, contraTradePA, contraClearingAcct, origControlDate, tradeModifier4Time, shortSaleIndicator, refReportingFacility, tradeModifier2Time, tradeReportRefID }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have processCode := readOptional_part [56, 49] record.processCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have mDMkt := readOptional_part [50, 55, 53] record.mDMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeCondition := readOptional_part [50, 55, 55] record.tradeCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have secondaryExecId := readOptional_part [53, 50, 55] record.secondaryExecId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have tradeReportID := readOptional_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have clearingInstruction := readOptional_part [53, 55, 55] record.clearingInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have reversalIndicator := readOptional_part [55, 48, 48] record.reversalIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have trdSubType := readRequired_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have publishTrdIndicator := readOptional_part [56, 53, 50] record.publishTrdIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have shortSaleReason := readOptional_part [56, 53, 51] record.shortSaleReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have asOfIndicator := readOptional_part [53, 48, 56, 48] record.asOfIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have relatedMarketCenter := readOptional_part [57, 50, 55, 55] record.relatedMarketCenter tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have advertisementInstruction := readOptional_part [57, 50, 55, 56] record.advertisementInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have clearingPrice := readOptional_part [57, 56, 50, 50] record.clearingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have reportingGUID := readOptional_part [57, 56, 50, 53] record.reportingGUID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nonReportingGUID := readOptional_part [57, 56, 50, 54] record.nonReportingGUID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have overrideFlag := readOptional_part [57, 56, 53, 52] record.overrideFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have contraBranchSeqNbr := readOptional_part [57, 56, 54, 48] record.contraBranchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have contraTradePA := readOptional_part [57, 56, 54, 50] record.contraTradePA tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have contraClearingAcct := readOptional_part [57, 56, 54, 51] record.contraClearingAcct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have origControlDate := readOptional_part [50, 50, 48, 49, 50] record.origControlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have tradeModifier4Time := readOptional_part [50, 50, 48, 49, 56] record.tradeModifier4Time tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have shortSaleIndicator := readOptional_part [50, 50, 48, 50, 52] record.shortSaleIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have refReportingFacility := readOptional_part [50, 50, 48, 50, 57] record.refReportingFacility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have tradeModifier2Time := readOptional_part [50, 50, 48, 51, 51] record.tradeModifier2Time tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, avgPx, clOrdID, cumQty, execID, execTransType, orderID, ordStatus, side, symbol, transactTime, symbolSfx, tradeDate, processCode, securityDesc, leavesQty, mDMkt, tradeCondition, contraBroker, priceType, clearingAccount, secondaryExecId, orderCapacity, tradeReportID, clearingInstruction, reversalIndicator, trdSubType, publishTrdIndicator, shortSaleReason, secondaryTrdType, tradeReportType, trdMatchID, asOfIndicator, memo, relatedMarketCenter, advertisementInstruction, clearingPrice, reportingGUID, nonReportingGUID, overrideFlag, contraBranchSeqNbr, contraTradePA, contraClearingAcct, origControlDate, tradeModifier4Time, shortSaleIndicator, refReportingFacility, tradeModifier2Time, tradeReportRefID, some_bind] <;> rfl

theorem TradeCaptureReport.taken (record : TradeCaptureReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [56, 49] record.processCode (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [50, 55, 53] record.mDMkt (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 55, 55] record.tradeCondition (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 50, 51] record.priceType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 50, 55] record.secondaryExecId (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [53, 55, 49] record.tradeReportID (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [53, 55, 55] record.clearingInstruction (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [55, 48, 48] record.reversalIndicator (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [56, 50, 57] record.trdSubType (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [56, 53, 50] record.publishTrdIndicator (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [56, 53, 51] record.shortSaleReason (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [56, 53, 53] record.secondaryTrdType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [56, 53, 54] record.tradeReportType (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [53, 48, 56, 48] record.asOfIndicator (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [57, 50, 55, 55] record.relatedMarketCenter (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [57, 50, 55, 56] record.advertisementInstruction (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 50] record.clearingPrice (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 53] record.reportingGUID (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 54] record.nonReportingGUID (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [57, 56, 53, 52] record.overrideFlag (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [57, 56, 54, 48] record.contraBranchSeqNbr (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [57, 56, 54, 50] record.contraTradePA (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 54, 51] record.contraClearingAcct (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 49, 50] record.origControlDate (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 49, 56] record.tradeModifier4Time (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 50, 52] record.shortSaleIndicator (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 50, 57] record.refReportingFacility (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 51, 51] record.tradeModifier2Time (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [53, 55, 50] record.tradeReportRefID (by decide) (by decide))
                                                  (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))

structure TradeCaptureReportTradeReport where
  partyRole : Option (Terminated 1)  -- tag 452
  branchSeqNbr : Option (Terminated 1)  -- tag 9861

def TradeCaptureReportTradeReport.parts (record : TradeCaptureReportTradeReport) : List Part :=
  [Part.optional [52, 53, 50] record.partyRole,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr]

def TradeCaptureReportTradeReport.tags : List (List (List UInt8)) :=
  [[[52, 53, 50]], [[57, 56, 54, 49]]]

theorem TradeCaptureReportTradeReport.shape (record : TradeCaptureReportTradeReport) : record.parts.map Part.tags = TradeCaptureReportTradeReport.tags := rfl

def TradeCaptureReportTradeReport.decode (tokens : List Token) : Option TradeCaptureReportTradeReport := do
  let partyRole ← readOptional [52, 53, 50] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  pure { partyRole, branchSeqNbr }

theorem TradeCaptureReportTradeReport.decode_agrees (record : TradeCaptureReportTradeReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportTradeReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportTradeReport.decode tokens = some record := by
  have distinct : TradeCaptureReportTradeReport.tags.flatten.Nodup := by decide +kernel
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [TradeCaptureReportTradeReport.decode, partyRole, branchSeqNbr, some_bind] <;> rfl

theorem TradeCaptureReportTradeReport.taken (record : TradeCaptureReportTradeReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 53, 50] record.partyRole (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 56, 54, 49] record.branchSeqNbr (by decide) (by decide))
    (paired_none pairing))

structure TradeCaptureReportStatus where
  text : Option (Terminated 1)  -- tag 58
  clientID : Option (Terminated 1)  -- tag 109
  secondaryTradeReportRefID : Option (Terminated 1)  -- tag 881
  trdRptStatus : Option (Terminated 1)  -- tag 939
  regFeeFlag : Option (Terminated 1)  -- tag 9807
  lockedIn : Option (Terminated 1)  -- tag 9857
  lockedInStatus : Option (Terminated 1)  -- tag 9847
  breakIndicator : Option (Terminated 1)  -- tag 9856
  clearingBroker : Option (Terminated 1)  -- tag 9824
  introBrokerInd : Option (Terminated 1)  -- tag 9830
  execBrokerInd : Option (Terminated 1)  -- tag 9831
  clearBrokerInd : Option (Terminated 1)  -- tag 9832
  responsibilityInd : Option (Terminated 1)  -- tag 9833
  tradeRepAvailInd : Option (Terminated 1)  -- tag 9834
  majorClearingInd : Option (Terminated 1)  -- tag 9835
  reserved : Option (Terminated 1)  -- tag 9836
  inhibitTradeIndicator : Option (Terminated 1)  -- tag 9819
  heldTradeStartTime : Option (Terminated 1)  -- tag 9820
  allowInhibitActionTime : Option (Terminated 1)  -- tag 9821

def TradeCaptureReportStatus.parts (record : TradeCaptureReportStatus) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [56, 56, 49] record.secondaryTradeReportRefID,
   Part.optional [57, 51, 57] record.trdRptStatus,
   Part.optional [57, 56, 48, 55] record.regFeeFlag,
   Part.optional [57, 56, 53, 55] record.lockedIn,
   Part.optional [57, 56, 52, 55] record.lockedInStatus,
   Part.optional [57, 56, 53, 54] record.breakIndicator,
   Part.optional [57, 56, 50, 52] record.clearingBroker,
   Part.optional [57, 56, 51, 48] record.introBrokerInd,
   Part.optional [57, 56, 51, 49] record.execBrokerInd,
   Part.optional [57, 56, 51, 50] record.clearBrokerInd,
   Part.optional [57, 56, 51, 51] record.responsibilityInd,
   Part.optional [57, 56, 51, 52] record.tradeRepAvailInd,
   Part.optional [57, 56, 51, 53] record.majorClearingInd,
   Part.optional [57, 56, 51, 54] record.reserved,
   Part.optional [57, 56, 49, 57] record.inhibitTradeIndicator,
   Part.optional [57, 56, 50, 48] record.heldTradeStartTime,
   Part.optional [57, 56, 50, 49] record.allowInhibitActionTime]

def TradeCaptureReportStatus.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[49, 48, 57]], [[56, 56, 49]], [[57, 51, 57]], [[57, 56, 48, 55]], [[57, 56, 53, 55]], [[57, 56, 52, 55]], [[57, 56, 53, 54]], [[57, 56, 50, 52]], [[57, 56, 51, 48]], [[57, 56, 51, 49]], [[57, 56, 51, 50]], [[57, 56, 51, 51]], [[57, 56, 51, 52]], [[57, 56, 51, 53]], [[57, 56, 51, 54]], [[57, 56, 49, 57]], [[57, 56, 50, 48]], [[57, 56, 50, 49]]]

theorem TradeCaptureReportStatus.shape (record : TradeCaptureReportStatus) : record.parts.map Part.tags = TradeCaptureReportStatus.tags := rfl

def TradeCaptureReportStatus.decode (tokens : List Token) : Option TradeCaptureReportStatus := do
  let text ← readOptional [53, 56] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let secondaryTradeReportRefID ← readOptional [56, 56, 49] tokens
  let trdRptStatus ← readOptional [57, 51, 57] tokens
  let regFeeFlag ← readOptional [57, 56, 48, 55] tokens
  let lockedIn ← readOptional [57, 56, 53, 55] tokens
  let lockedInStatus ← readOptional [57, 56, 52, 55] tokens
  let breakIndicator ← readOptional [57, 56, 53, 54] tokens
  let clearingBroker ← readOptional [57, 56, 50, 52] tokens
  let introBrokerInd ← readOptional [57, 56, 51, 48] tokens
  let execBrokerInd ← readOptional [57, 56, 51, 49] tokens
  let clearBrokerInd ← readOptional [57, 56, 51, 50] tokens
  let responsibilityInd ← readOptional [57, 56, 51, 51] tokens
  let tradeRepAvailInd ← readOptional [57, 56, 51, 52] tokens
  let majorClearingInd ← readOptional [57, 56, 51, 53] tokens
  let reserved ← readOptional [57, 56, 51, 54] tokens
  let inhibitTradeIndicator ← readOptional [57, 56, 49, 57] tokens
  let heldTradeStartTime ← readOptional [57, 56, 50, 48] tokens
  let allowInhibitActionTime ← readOptional [57, 56, 50, 49] tokens
  pure { text, clientID, secondaryTradeReportRefID, trdRptStatus, regFeeFlag, lockedIn, lockedInStatus, breakIndicator, clearingBroker, introBrokerInd, execBrokerInd, clearBrokerInd, responsibilityInd, tradeRepAvailInd, majorClearingInd, reserved, inhibitTradeIndicator, heldTradeStartTime, allowInhibitActionTime }

theorem TradeCaptureReportStatus.decode_agrees (record : TradeCaptureReportStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportStatus.decode tokens = some record := by
  have distinct : TradeCaptureReportStatus.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryTradeReportRefID := readOptional_part [56, 56, 49] record.secondaryTradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have trdRptStatus := readOptional_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have regFeeFlag := readOptional_part [57, 56, 48, 55] record.regFeeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lockedIn := readOptional_part [57, 56, 53, 55] record.lockedIn tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lockedInStatus := readOptional_part [57, 56, 52, 55] record.lockedInStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have breakIndicator := readOptional_part [57, 56, 53, 54] record.breakIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clearingBroker := readOptional_part [57, 56, 50, 52] record.clearingBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have introBrokerInd := readOptional_part [57, 56, 51, 48] record.introBrokerInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execBrokerInd := readOptional_part [57, 56, 51, 49] record.execBrokerInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clearBrokerInd := readOptional_part [57, 56, 51, 50] record.clearBrokerInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have responsibilityInd := readOptional_part [57, 56, 51, 51] record.responsibilityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeRepAvailInd := readOptional_part [57, 56, 51, 52] record.tradeRepAvailInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have majorClearingInd := readOptional_part [57, 56, 51, 53] record.majorClearingInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have reserved := readOptional_part [57, 56, 51, 54] record.reserved tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have inhibitTradeIndicator := readOptional_part [57, 56, 49, 57] record.inhibitTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have heldTradeStartTime := readOptional_part [57, 56, 50, 48] record.heldTradeStartTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have allowInhibitActionTime := readOptional_part [57, 56, 50, 49] record.allowInhibitActionTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [TradeCaptureReportStatus.decode, text, clientID, secondaryTradeReportRefID, trdRptStatus, regFeeFlag, lockedIn, lockedInStatus, breakIndicator, clearingBroker, introBrokerInd, execBrokerInd, clearBrokerInd, responsibilityInd, tradeRepAvailInd, majorClearingInd, reserved, inhibitTradeIndicator, heldTradeStartTime, allowInhibitActionTime, some_bind] <;> rfl

theorem TradeCaptureReportStatus.taken (record : TradeCaptureReportStatus) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [56, 56, 49] record.secondaryTradeReportRefID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57] record.trdRptStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 56, 48, 55] record.regFeeFlag (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 56, 53, 55] record.lockedIn (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 56, 52, 55] record.lockedInStatus (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 56, 53, 54] record.breakIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 52] record.clearingBroker (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 48] record.introBrokerInd (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 49] record.execBrokerInd (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 50] record.clearBrokerInd (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 51] record.responsibilityInd (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 52] record.tradeRepAvailInd (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 53] record.majorClearingInd (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 56, 51, 54] record.reserved (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 56, 49, 57] record.inhibitTradeIndicator (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 48] record.heldTradeStartTime (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 56, 50, 49] record.allowInhibitActionTime (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | tradeCaptureReportTradeReport (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeReport)
  | tradeCaptureReportStatus (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportStatus)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportTradeReport header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportStatus header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
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
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [70] then
            if known (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportTradeReport.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReport.decode rest
              let r1 ← TradeCaptureReportTradeReport.decode rest
              pure (.tradeCaptureReportTradeReport header r0 r1)
            else none
          else if key.val = [73] then
            if known (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportStatus.tags) rest then do
              let header ← Header.decode rest
              let r0 ← TradeCaptureReport.decode rest
              let r1 ← TradeCaptureReportStatus.decode rest
              pure (.tradeCaptureReportStatus header r0 r1)
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

theorem Message.decode_tradeCaptureReportTradeReport (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeReport) :
    Message.decode (Message.tokens (.tradeCaptureReportTradeReport header r0 r1)) = some (.tradeCaptureReportTradeReport header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportTradeReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReport.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportTradeReport.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[70], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReport.tags) ([[[49, 53, 48]]]) (TradeCaptureReportTradeReport.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportTradeReport.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportTradeReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportTradeReport.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportStatus (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportStatus) :
    Message.decode (Message.tokens (.tradeCaptureReportStatus header r0 r1)) = some (.tradeCaptureReportStatus header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) ([]) (Header.tags) (TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportStatus.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.tags) (TradeCaptureReport.tags) ([[[49, 53, 48]]] ++ TradeCaptureReportStatus.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[73], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[73], by decide⟩]) (r1.parts) (Header.tags ++ TradeCaptureReport.tags) ([[[49, 53, 48]]]) (TradeCaptureReportStatus.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := TradeCaptureReportStatus.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩]) (r1.parts) ([]) (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]]) (TradeCaptureReportStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.tags ++ TradeCaptureReport.tags ++ [[[49, 53, 48]]] ++ TradeCaptureReportStatus.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | tradeCaptureReportTradeReport header r0 r1 => exact Message.decode_tradeCaptureReportTradeReport header r0 r1
  | tradeCaptureReportStatus header r0 r1 => exact Message.decode_tradeCaptureReportStatus header r0 r1

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_tradeCaptureReportTradeReport (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportTradeReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportTradeReport header r0 r1)) = some (.tradeCaptureReportTradeReport header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (TradeCaptureReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[70], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[70], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (TradeCaptureReportTradeReport.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportTradeReport header r0 r1

theorem Message.decodeBytes_tradeCaptureReportStatus (header : Header) (r0 : TradeCaptureReport) (r1 : TradeCaptureReportStatus) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportStatus header r0 r1)) = some (.tradeCaptureReportStatus header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (TradeCaptureReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[73], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[73], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[73], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (TradeCaptureReportStatus.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportStatus header r0 r1

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | tradeCaptureReportTradeReport header r0 r1 => exact Message.decodeBytes_tradeCaptureReportTradeReport header r0 r1
  | tradeCaptureReportStatus header r0 r1 => exact Message.decodeBytes_tradeCaptureReportStatus header r0 r1

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNsmequitiesTradereportingFixV20261Exchange
