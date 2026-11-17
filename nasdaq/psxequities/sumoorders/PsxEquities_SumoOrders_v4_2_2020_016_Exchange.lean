import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v4.2.2020.016, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqPsxequitiesSumoordersFixV422020016Exchange

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
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
   Part.optional [53, 48] record.senderSubID,
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
  let senderSubID ← readOptional [53, 48] tokens
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
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
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
     (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
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
  memo : Option (Terminated 1)  -- tag 5149

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagId,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 49, 52, 57] record.memo]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 49, 52, 57]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagId ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { refSeqNum, text, refTagId, refMsgType, sessionRejectReason, memo }

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
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagId, refMsgType, sessionRejectReason, memo, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagId (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
        (paired_none pairing))))))

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdID : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execTransType : Terminated 1  -- tag 20
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  maxFloor : Option (Terminated 1)  -- tag 111
  leavesQty : Terminated 1  -- tag 151

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 53, 49] record.leavesQty]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[49, 56]], [[50, 48]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[49, 49, 49]], [[49, 53, 49]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execTransType ← readRequired [50, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  pure { account, avgPx, clOrdID, cumQty, execID, execInst, execTransType, orderID, orderQty, ordStatus, ordType, price, side, symbol, timeInForce, maxFloor, leavesQty }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, cumQty, execID, execInst, execTransType, orderID, orderQty, ordStatus, ordType, price, side, symbol, timeInForce, maxFloor, leavesQty, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                   (paired_none pairing)))))))))))))))))

structure ExecutionReportNew where
  currency : Option (Terminated 1)  -- tag 15
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149

def ExecutionReportNew.parts (record : ExecutionReportNew) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo]

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[54, 53]], [[49, 49, 48]], [[50, 49, 49]], [[51, 51, 54]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]]]

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (tokens : List Token) : Option ExecutionReportNew := do
  let currency ← readOptional [49, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { currency, symbolSfx, minQty, pegDifference, tradingSessionID, discretionInst, discretionOffset, memo }

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  have distinct : ExecutionReportNew.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [ExecutionReportNew.decode, currency, symbolSfx, minQty, pegDifference, tradingSessionID, discretionInst, discretionOffset, memo, some_bind] <;> rfl

theorem ExecutionReportNew.taken (record : ExecutionReportNew) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
          (paired_none pairing))))))))

structure ExecutionReportPartialFill where
  currency : Option (Terminated 1)  -- tag 15
  execRefID : Option (Terminated 1)  -- tag 19
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  origClOrdID : Terminated 1  -- tag 41
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  contraBroker : Option (Terminated 1)  -- tag 375
  noContraBrokers : Option (Terminated 1)  -- tag 382
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149
  tradeThruFlag : Option (Terminated 1)  -- tag 9231
  liqProvFlg : Terminated 1  -- tag 9730
  reserveSize : Option (Terminated 1)  -- tag 9870
  displaySize : Option (Terminated 1)  -- tag 9872

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [49, 57] record.execRefID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo,
   Part.optional [57, 50, 51, 49] record.tradeThruFlag,
   Part.required [57, 55, 51, 48] record.liqProvFlg,
   Part.optional [57, 56, 55, 48] record.reserveSize,
   Part.optional [57, 56, 55, 50] record.displaySize]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[49, 57]], [[51, 49]], [[51, 50]], [[52, 49]], [[54, 48]], [[54, 53]], [[55, 54]], [[49, 49, 48]], [[50, 49, 49]], [[51, 51, 54]], [[51, 55, 53]], [[51, 56, 50]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]], [[57, 50, 51, 49]], [[57, 55, 51, 48]], [[57, 56, 55, 48]], [[57, 56, 55, 50]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let currency ← readOptional [49, 53] tokens
  let execRefID ← readOptional [49, 57] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  let tradeThruFlag ← readOptional [57, 50, 51, 49] tokens
  let liqProvFlg ← readRequired [57, 55, 51, 48] tokens
  let reserveSize ← readOptional [57, 56, 55, 48] tokens
  let displaySize ← readOptional [57, 56, 55, 50] tokens
  pure { currency, execRefID, lastPx, lastShares, origClOrdID, transactTime, symbolSfx, execBroker, minQty, pegDifference, tradingSessionID, contraBroker, noContraBrokers, discretionInst, discretionOffset, memo, tradeThruFlag, liqProvFlg, reserveSize, displaySize }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeThruFlag := readOptional_part [57, 50, 51, 49] record.tradeThruFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have liqProvFlg := readRequired_part [57, 55, 51, 48] record.liqProvFlg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have reserveSize := readOptional_part [57, 56, 55, 48] record.reserveSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have displaySize := readOptional_part [57, 56, 55, 50] record.displaySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, currency, execRefID, lastPx, lastShares, origClOrdID, transactTime, symbolSfx, execBroker, minQty, pegDifference, tradingSessionID, contraBroker, noContraBrokers, discretionInst, discretionOffset, memo, tradeThruFlag, liqProvFlg, reserveSize, displaySize, some_bind] <;> rfl

theorem ExecutionReportPartialFill.taken (record : ExecutionReportPartialFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 50] record.noContraBrokers (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 51, 49] record.tradeThruFlag (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [57, 55, 51, 48] record.liqProvFlg (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 48] record.reserveSize (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 50] record.displaySize (by decide) (by decide))
                      (paired_none pairing))))))))))))))))))))

structure ExecutionReportFill where
  currency : Option (Terminated 1)  -- tag 15
  execRefID : Option (Terminated 1)  -- tag 19
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  origClOrdID : Terminated 1  -- tag 41
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  contraBroker : Option (Terminated 1)  -- tag 375
  noContraBrokers : Option (Terminated 1)  -- tag 382
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149
  tradeThruFlag : Option (Terminated 1)  -- tag 9231
  liqProvFlg : Terminated 1  -- tag 9730
  reserveSize : Option (Terminated 1)  -- tag 9870
  displaySize : Option (Terminated 1)  -- tag 9872

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [49, 57] record.execRefID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo,
   Part.optional [57, 50, 51, 49] record.tradeThruFlag,
   Part.required [57, 55, 51, 48] record.liqProvFlg,
   Part.optional [57, 56, 55, 48] record.reserveSize,
   Part.optional [57, 56, 55, 50] record.displaySize]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[49, 57]], [[51, 49]], [[51, 50]], [[52, 49]], [[54, 48]], [[54, 53]], [[55, 54]], [[49, 49, 48]], [[50, 49, 49]], [[51, 51, 54]], [[51, 55, 53]], [[51, 56, 50]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]], [[57, 50, 51, 49]], [[57, 55, 51, 48]], [[57, 56, 55, 48]], [[57, 56, 55, 50]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let currency ← readOptional [49, 53] tokens
  let execRefID ← readOptional [49, 57] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  let tradeThruFlag ← readOptional [57, 50, 51, 49] tokens
  let liqProvFlg ← readRequired [57, 55, 51, 48] tokens
  let reserveSize ← readOptional [57, 56, 55, 48] tokens
  let displaySize ← readOptional [57, 56, 55, 50] tokens
  pure { currency, execRefID, lastPx, lastShares, origClOrdID, transactTime, symbolSfx, execBroker, minQty, pegDifference, tradingSessionID, contraBroker, noContraBrokers, discretionInst, discretionOffset, memo, tradeThruFlag, liqProvFlg, reserveSize, displaySize }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeThruFlag := readOptional_part [57, 50, 51, 49] record.tradeThruFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have liqProvFlg := readRequired_part [57, 55, 51, 48] record.liqProvFlg tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have reserveSize := readOptional_part [57, 56, 55, 48] record.reserveSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have displaySize := readOptional_part [57, 56, 55, 50] record.displaySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, currency, execRefID, lastPx, lastShares, origClOrdID, transactTime, symbolSfx, execBroker, minQty, pegDifference, tradingSessionID, contraBroker, noContraBrokers, discretionInst, discretionOffset, memo, tradeThruFlag, liqProvFlg, reserveSize, displaySize, some_bind] <;> rfl

theorem ExecutionReportFill.taken (record : ExecutionReportFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 50] record.noContraBrokers (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 51, 49] record.tradeThruFlag (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [57, 55, 51, 48] record.liqProvFlg (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 48] record.reserveSize (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 50] record.displaySize (by decide) (by decide))
                      (paired_none pairing))))))))))))))))))))

structure ExecutionReportRestated where
  execBroker : Terminated 1  -- tag 76
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  execRefID : Option (Terminated 1)  -- tag 19
  pegDifference : Option (Terminated 1)  -- tag 211
  origClOrdID : Option (Terminated 1)  -- tag 41
  clientID : Option (Terminated 1)  -- tag 109
  displayInst : Option (Terminated 1)  -- tag 9140
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  rule80AOrderCapacity : Option (Terminated 1)  -- tag 47
  text : Option (Terminated 1)  -- tag 58
  liquidityFlag : Option (Terminated 1)  -- tag 9882
  execRestatementReason : Terminated 1  -- tag 378

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.required [55, 54] record.execBroker,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [49, 57] record.execRefID,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 49, 52, 48] record.displayInst,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [52, 55] record.rule80AOrderCapacity,
   Part.optional [53, 56] record.text,
   Part.optional [57, 56, 56, 50] record.liquidityFlag,
   Part.required [51, 55, 56] record.execRestatementReason]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[55, 54]], [[51, 50]], [[51, 49]], [[49, 57]], [[50, 49, 49]], [[52, 49]], [[49, 48, 57]], [[57, 49, 52, 48]], [[55, 53]], [[54, 48]], [[52, 55]], [[53, 56]], [[57, 56, 56, 50]], [[51, 55, 56]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let execBroker ← readRequired [55, 54] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let execRefID ← readOptional [49, 57] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let displayInst ← readOptional [57, 49, 52, 48] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let rule80AOrderCapacity ← readOptional [52, 55] tokens
  let text ← readOptional [53, 56] tokens
  let liquidityFlag ← readOptional [57, 56, 56, 50] tokens
  let execRestatementReason ← readRequired [51, 55, 56] tokens
  pure { execBroker, lastShares, lastPx, execRefID, pegDifference, origClOrdID, clientID, displayInst, tradeDate, transactTime, rule80AOrderCapacity, text, liquidityFlag, execRestatementReason }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have execBroker := readRequired_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have displayInst := readOptional_part [57, 49, 52, 48] record.displayInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have rule80AOrderCapacity := readOptional_part [52, 55] record.rule80AOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have liquidityFlag := readOptional_part [57, 56, 56, 50] record.liquidityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execRestatementReason := readRequired_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, execBroker, lastShares, lastPx, execRefID, pegDifference, origClOrdID, clientID, displayInst, tradeDate, transactTime, rule80AOrderCapacity, text, liquidityFlag, execRestatementReason, some_bind] <;> rfl

theorem ExecutionReportRestated.taken (record : ExecutionReportRestated) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55, 54] record.execBroker (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 49, 52, 48] record.displayInst (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80AOrderCapacity (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.liquidityFlag (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
                (paired_none pairing))))))))))))))

structure ExecutionReportRejected where
  currency : Option (Terminated 1)  -- tag 15
  text : Option (Terminated 1)  -- tag 58
  symbolSfx : Option (Terminated 1)  -- tag 65
  ordRejReason : Option (Terminated 1)  -- tag 103
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [53, 56] record.text,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[53, 56]], [[54, 53]], [[49, 48, 51]], [[49, 49, 48]], [[50, 49, 49]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let currency ← readOptional [49, 53] tokens
  let text ← readOptional [53, 56] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { currency, text, symbolSfx, ordRejReason, minQty, pegDifference, discretionInst, discretionOffset, memo }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, currency, text, symbolSfx, ordRejReason, minQty, pegDifference, discretionInst, discretionOffset, memo, some_bind] <;> rfl

theorem ExecutionReportRejected.taken (record : ExecutionReportRejected) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
           (paired_none pairing)))))))))

structure ExecutionReportPendingCancel where
  currency : Option (Terminated 1)  -- tag 15
  origClOrdID : Terminated 1  -- tag 41
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149

def ExecutionReportPendingCancel.parts (record : ExecutionReportPendingCancel) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo]

def ExecutionReportPendingCancel.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[52, 49]], [[54, 53]], [[49, 49, 48]], [[50, 49, 49]], [[51, 51, 54]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]]]

theorem ExecutionReportPendingCancel.shape (record : ExecutionReportPendingCancel) : record.parts.map Part.tags = ExecutionReportPendingCancel.tags := rfl

def ExecutionReportPendingCancel.decode (tokens : List Token) : Option ExecutionReportPendingCancel := do
  let currency ← readOptional [49, 53] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { currency, origClOrdID, symbolSfx, minQty, pegDifference, tradingSessionID, discretionInst, discretionOffset, memo }

theorem ExecutionReportPendingCancel.decode_agrees (record : ExecutionReportPendingCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPendingCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPendingCancel.decode tokens = some record := by
  have distinct : ExecutionReportPendingCancel.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [ExecutionReportPendingCancel.decode, currency, origClOrdID, symbolSfx, minQty, pegDifference, tradingSessionID, discretionInst, discretionOffset, memo, some_bind] <;> rfl

theorem ExecutionReportPendingCancel.taken (record : ExecutionReportPendingCancel) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
           (paired_none pairing)))))))))

structure ExecutionReportCanceled where
  currency : Option (Terminated 1)  -- tag 15
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  origClOrdID : Terminated 1  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149
  reserveSize : Option (Terminated 1)  -- tag 9870
  displaySize : Option (Terminated 1)  -- tag 9872

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo,
   Part.optional [57, 56, 55, 48] record.reserveSize,
   Part.optional [57, 56, 55, 50] record.displaySize]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[51, 49]], [[51, 50]], [[52, 49]], [[53, 56]], [[54, 53]], [[49, 49, 48]], [[50, 49, 49]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]], [[57, 56, 55, 48]], [[57, 56, 55, 50]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let currency ← readOptional [49, 53] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  let reserveSize ← readOptional [57, 56, 55, 48] tokens
  let displaySize ← readOptional [57, 56, 55, 50] tokens
  pure { currency, lastPx, lastShares, origClOrdID, text, symbolSfx, minQty, pegDifference, discretionInst, discretionOffset, memo, reserveSize, displaySize }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have reserveSize := readOptional_part [57, 56, 55, 48] record.reserveSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displaySize := readOptional_part [57, 56, 55, 50] record.displaySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, currency, lastPx, lastShares, origClOrdID, text, symbolSfx, minQty, pegDifference, discretionInst, discretionOffset, memo, reserveSize, displaySize, some_bind] <;> rfl

theorem ExecutionReportCanceled.taken (record : ExecutionReportCanceled) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 48] record.reserveSize (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 56, 55, 50] record.displaySize (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure ExecutionReportPendingReplace where
  currency : Option (Terminated 1)  -- tag 15
  origClOrdID : Terminated 1  -- tag 41
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  pegDifference : Option (Terminated 1)  -- tag 211
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  memo : Option (Terminated 1)  -- tag 5149

def ExecutionReportPendingReplace.parts (record : ExecutionReportPendingReplace) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 49, 52, 57] record.memo]

def ExecutionReportPendingReplace.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[52, 49]], [[54, 53]], [[49, 49, 48]], [[50, 49, 49]], [[51, 56, 56]], [[51, 56, 57]], [[53, 49, 52, 57]]]

theorem ExecutionReportPendingReplace.shape (record : ExecutionReportPendingReplace) : record.parts.map Part.tags = ExecutionReportPendingReplace.tags := rfl

def ExecutionReportPendingReplace.decode (tokens : List Token) : Option ExecutionReportPendingReplace := do
  let currency ← readOptional [49, 53] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { currency, origClOrdID, symbolSfx, minQty, pegDifference, discretionInst, discretionOffset, memo }

theorem ExecutionReportPendingReplace.decode_agrees (record : ExecutionReportPendingReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPendingReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPendingReplace.decode tokens = some record := by
  have distinct : ExecutionReportPendingReplace.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [ExecutionReportPendingReplace.decode, currency, origClOrdID, symbolSfx, minQty, pegDifference, discretionInst, discretionOffset, memo, some_bind] <;> rfl

theorem ExecutionReportPendingReplace.taken (record : ExecutionReportPendingReplace) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
          (paired_none pairing))))))))

structure OrderCancelReject where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  cxlRejReason : Option (Terminated 1)  -- tag 102
  memo : Option (Terminated 1)  -- tag 5149

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 49, 52, 57] record.memo]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[55, 54]], [[49, 48, 50]], [[53, 49, 52, 57]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { clOrdID, orderID, ordStatus, origClOrdID, text, execBroker, cxlRejReason, memo }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clOrdID, orderID, ordStatus, origClOrdID, text, execBroker, cxlRejReason, memo, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
          (paired_none pairing))))))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportPendingCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingCancel)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportPendingReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingReplace)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportPendingCancel header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportPendingReplace header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)

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
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNew.decode rest
              pure (.executionReportNew header r0 r1)
            else none
          else if key.val = [49] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPartialFill.decode rest
              pure (.executionReportPartialFill header r0 r1)
            else none
          else if key.val = [50] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportFill.decode rest
              pure (.executionReportFill header r0 r1)
            else none
          else if key.val = [68] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRestated.decode rest
              pure (.executionReportRestated header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [54] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingCancel.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPendingCancel.decode rest
              pure (.executionReportPendingCancel header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCanceled.decode rest
              pure (.executionReportCanceled header r0 r1)
            else none
          else if key.val = [69] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPendingReplace.decode rest
              pure (.executionReportPendingReplace header r0 r1)
            else none
          else none
      else if token.value = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
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

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decode (Message.tokens (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPartialFill.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPartialFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill) :
    Message.decode (Message.tokens (.executionReportFill header r0 r1)) = some (.executionReportFill header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportFill.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl
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

theorem Message.decode_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decode (Message.tokens (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportPendingCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingCancel) :
    Message.decode (Message.tokens (.executionReportPendingCancel header r0 r1)) = some (.executionReportPendingCancel header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingCancel.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPendingCancel.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[54], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[54], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPendingCancel.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPendingCancel.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPendingCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingCancel.tags) rfl
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

theorem Message.decode_executionReportPendingReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingReplace) :
    Message.decode (Message.tokens (.executionReportPendingReplace header r0 r1)) = some (.executionReportPendingReplace header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[69], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[69], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPendingReplace.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPendingReplace.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPendingReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportPendingCancel header r0 r1 => exact Message.decode_executionReportPendingCancel header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportPendingReplace header r0 r1 => exact Message.decode_executionReportPendingReplace header r0 r1
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0

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

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportNew.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decodeBytes (Message.encode (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[49], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[49], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportPartialFill.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPartialFill header r0 r1

theorem Message.decodeBytes_executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill) :
    Message.decodeBytes (Message.encode (.executionReportFill header r0 r1)) = some (.executionReportFill header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[50], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportFill.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFill header r0 r1

theorem Message.decodeBytes_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decodeBytes (Message.encode (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[68], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[68], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRestated.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRestated header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[56], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[56], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRejected.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportPendingCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingCancel) :
    Message.decodeBytes (Message.encode (.executionReportPendingCancel header r0 r1)) = some (.executionReportPendingCancel header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[54], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[54], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[54], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportPendingCancel.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPendingCancel header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[52], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[52], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportCanceled.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportPendingReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingReplace) :
    Message.decodeBytes (Message.encode (.executionReportPendingReplace header r0 r1)) = some (.executionReportPendingReplace header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[69], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[69], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[69], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportPendingReplace.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPendingReplace header r0 r1

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportPendingCancel header r0 r1 => exact Message.decodeBytes_executionReportPendingCancel header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportPendingReplace header r0 r1 => exact Message.decodeBytes_executionReportPendingReplace header r0 r1
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqPsxequitiesSumoordersFixV422020016Exchange
