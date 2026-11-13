import Wire

/-!
# The Members Exchange Order Entry v1.10, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.MemxMemxoptionsOrderentryFixV110Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime }

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
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

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
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  defaultApplVerID : Terminated 1  -- tag 1137
  defaultCstmApplVerID : Terminated 1  -- tag 1408

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.required [49, 52, 48, 56] record.defaultCstmApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[49, 49, 51, 55]], [[49, 52, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let defaultCstmApplVerID ← readRequired [49, 52, 48, 56] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, defaultApplVerID, defaultCstmApplVerID }

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
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defaultCstmApplVerID := readRequired_part [49, 52, 48, 56] record.defaultCstmApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, defaultApplVerID, defaultCstmApplVerID, some_bind] <;> rfl

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
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refTagID, refMsgType, text }

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
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, text, some_bind] <;> rfl

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

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Terminated 1  -- tag 102
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  symbol : Option (Terminated 1)  -- tag 55
  maturityDate : Option (Terminated 1)  -- tag 541
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Terminated 1  -- tag 54

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.required [49, 48, 50] record.cxlRejReason,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[52, 51, 52]], [[49, 48, 50]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readRequired [49, 48, 50] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, cxlRejReason, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejReason := readRequired_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, cxlRejResponseTo, cxlRejReason, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, some_bind] <;> rfl

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  execID : Terminated 1  -- tag 17
  ordStatus : Terminated 1  -- tag 39
  symbol : Terminated 1  -- tag 55
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  side : Terminated 1  -- tag 54
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  transactTime : Terminated 1  -- tag 60

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 55] record.execID,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [54, 48] record.transactTime]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[49, 55]], [[51, 57]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[49, 53, 49]], [[49, 52]], [[52, 52]], [[51, 56]], [[54, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { orderID, clOrdID, execID, ordStatus, symbol, maturityDate, putOrCall, strikePrice, side, leavesQty, cumQty, price, orderQty, transactTime }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, execID, ordStatus, symbol, maturityDate, putOrCall, strikePrice, side, leavesQty, cumQty, price, orderQty, transactTime, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
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

structure ExecutionReportNew where
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  repriceFrequency : Option (Terminated 1)  -- tag 21020
  repriceBehaviorType : Option (Terminated 1)  -- tag 21021
  ordType : Terminated 1  -- tag 40
  timeInForce : Terminated 1  -- tag 59
  positionEffect : Option (Terminated 1)  -- tag 77
  tradingCapacity : Terminated 1  -- tag 1815
  execInst : Terminated 1  -- tag 18
  mtpGroupID : Option (Terminated 1)  -- tag 2362
  matchTradePrevention : Option (Terminated 1)  -- tag 21001
  riskGroupID : Option (Terminated 1)  -- tag 21005
  cancelGroupID : Option (Terminated 1)  -- tag 21000
  noPartyIDs : List NoPartyIDs  -- tag 453

def ExecutionReportNew.parts (record : ExecutionReportNew) : List Part :=
  [Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [50, 49, 48, 50, 48] record.repriceFrequency,
   Part.optional [50, 49, 48, 50, 49] record.repriceBehaviorType,
   Part.required [52, 48] record.ordType,
   Part.required [53, 57] record.timeInForce,
   Part.optional [55, 55] record.positionEffect,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.required [49, 56] record.execInst,
   Part.optional [50, 51, 54, 50] record.mtpGroupID,
   Part.optional [50, 49, 48, 48, 49] record.matchTradePrevention,
   Part.optional [50, 49, 48, 48, 53] record.riskGroupID,
   Part.optional [50, 49, 48, 48, 48] record.cancelGroupID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 51, 53]], [[50, 49, 48, 50, 48]], [[50, 49, 48, 50, 49]], [[52, 48]], [[53, 57]], [[55, 55]], [[49, 56, 49, 53]], [[49, 56]], [[50, 51, 54, 50]], [[50, 49, 48, 48, 49]], [[50, 49, 48, 48, 53]], [[50, 49, 48, 48, 48]], [52, 53, 51] :: NoPartyIDs.members]

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (tokens : List Token) : Option ExecutionReportNew := do
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let repriceFrequency ← readOptional [50, 49, 48, 50, 48] tokens
  let repriceBehaviorType ← readOptional [50, 49, 48, 50, 49] tokens
  let ordType ← readRequired [52, 48] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let execInst ← readRequired [49, 56] tokens
  let mtpGroupID ← readOptional [50, 51, 54, 50] tokens
  let matchTradePrevention ← readOptional [50, 49, 48, 48, 49] tokens
  let riskGroupID ← readOptional [50, 49, 48, 48, 53] tokens
  let cancelGroupID ← readOptional [50, 49, 48, 48, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { optionsSecurityID, repriceFrequency, repriceBehaviorType, ordType, timeInForce, positionEffect, tradingCapacity, execInst, mtpGroupID, matchTradePrevention, riskGroupID, cancelGroupID, noPartyIDs }

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  have distinct : ExecutionReportNew.tags.flatten.Nodup := by decide +kernel
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have repriceFrequency := readOptional_part [50, 49, 48, 50, 48] record.repriceFrequency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have repriceBehaviorType := readOptional_part [50, 49, 48, 50, 49] record.repriceBehaviorType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execInst := readRequired_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have mtpGroupID := readOptional_part [50, 51, 54, 50] record.mtpGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have matchTradePrevention := readOptional_part [50, 49, 48, 48, 49] record.matchTradePrevention tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have riskGroupID := readOptional_part [50, 49, 48, 48, 53] record.riskGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have cancelGroupID := readOptional_part [50, 49, 48, 48, 48] record.cancelGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [ExecutionReportNew.decode, optionsSecurityID, repriceFrequency, repriceBehaviorType, ordType, timeInForce, positionEffect, tradingCapacity, execInst, mtpGroupID, matchTradePrevention, riskGroupID, cancelGroupID, noPartyIDs, some_bind] <;> rfl

structure ExecutionReportRejected where
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  ordType : Terminated 1  -- tag 40
  ordRejReason : Terminated 1  -- tag 103

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [52, 48] record.ordType,
   Part.required [49, 48, 51] record.ordRejReason]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 51, 53]], [[52, 48]], [[49, 48, 51]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let ordType ← readRequired [52, 48] tokens
  let ordRejReason ← readRequired [49, 48, 51] tokens
  pure { optionsSecurityID, ordType, ordRejReason }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, optionsSecurityID, ordType, ordRejReason, some_bind] <;> rfl

structure ExecutionReportTrade where
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  ordType : Terminated 1  -- tag 40
  trdMatchID : Terminated 1  -- tag 880
  lastLiquidityInd : Terminated 1  -- tag 851
  lastMkt : Terminated 1  -- tag 30
  positionEffect : Option (Terminated 1)  -- tag 77
  tradingCapacity : Terminated 1  -- tag 1815
  contraTradingCapacity : Option (Terminated 1)  -- tag 21036
  noPartyIDs : List NoPartyIDs  -- tag 453

def ExecutionReportTrade.parts (record : ExecutionReportTrade) : List Part :=
  [Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.required [52, 48] record.ordType,
   Part.required [56, 56, 48] record.trdMatchID,
   Part.required [56, 53, 49] record.lastLiquidityInd,
   Part.required [51, 48] record.lastMkt,
   Part.optional [55, 55] record.positionEffect,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [50, 49, 48, 51, 54] record.contraTradingCapacity,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def ExecutionReportTrade.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 51, 53]], [[51, 50]], [[51, 49]], [[52, 48]], [[56, 56, 48]], [[56, 53, 49]], [[51, 48]], [[55, 55]], [[49, 56, 49, 53]], [[50, 49, 48, 51, 54]], [52, 53, 51] :: NoPartyIDs.members]

theorem ExecutionReportTrade.shape (record : ExecutionReportTrade) : record.parts.map Part.tags = ExecutionReportTrade.tags := rfl

def ExecutionReportTrade.decode (tokens : List Token) : Option ExecutionReportTrade := do
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let ordType ← readRequired [52, 48] tokens
  let trdMatchID ← readRequired [56, 56, 48] tokens
  let lastLiquidityInd ← readRequired [56, 53, 49] tokens
  let lastMkt ← readRequired [51, 48] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let contraTradingCapacity ← readOptional [50, 49, 48, 51, 54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { optionsSecurityID, lastQty, lastPx, ordType, trdMatchID, lastLiquidityInd, lastMkt, positionEffect, tradingCapacity, contraTradingCapacity, noPartyIDs }

theorem ExecutionReportTrade.decode_agrees (record : ExecutionReportTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTrade.decode tokens = some record := by
  have distinct : ExecutionReportTrade.tags.flatten.Nodup := by decide +kernel
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastLiquidityInd := readRequired_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastMkt := readRequired_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contraTradingCapacity := readOptional_part [50, 49, 48, 51, 54] record.contraTradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportTrade.decode, optionsSecurityID, lastQty, lastPx, ordType, trdMatchID, lastLiquidityInd, lastMkt, positionEffect, tradingCapacity, contraTradingCapacity, noPartyIDs, some_bind] <;> rfl

structure ExecutionReportPendingReplace where
  origClOrdID : Terminated 1  -- tag 41
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  ordType : Terminated 1  -- tag 40

def ExecutionReportPendingReplace.parts (record : ExecutionReportPendingReplace) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [52, 48] record.ordType]

def ExecutionReportPendingReplace.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[50, 49, 48, 51, 53]], [[52, 48]]]

theorem ExecutionReportPendingReplace.shape (record : ExecutionReportPendingReplace) : record.parts.map Part.tags = ExecutionReportPendingReplace.tags := rfl

def ExecutionReportPendingReplace.decode (tokens : List Token) : Option ExecutionReportPendingReplace := do
  let origClOrdID ← readRequired [52, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let ordType ← readRequired [52, 48] tokens
  pure { origClOrdID, optionsSecurityID, ordType }

theorem ExecutionReportPendingReplace.decode_agrees (record : ExecutionReportPendingReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPendingReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPendingReplace.decode tokens = some record := by
  have distinct : ExecutionReportPendingReplace.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportPendingReplace.decode, origClOrdID, optionsSecurityID, ordType, some_bind] <;> rfl

structure ExecutionReportReplaced where
  origClOrdID : Terminated 1  -- tag 41
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  ordType : Terminated 1  -- tag 40

def ExecutionReportReplaced.parts (record : ExecutionReportReplaced) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [52, 48] record.ordType]

def ExecutionReportReplaced.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[50, 49, 48, 51, 53]], [[52, 48]]]

theorem ExecutionReportReplaced.shape (record : ExecutionReportReplaced) : record.parts.map Part.tags = ExecutionReportReplaced.tags := rfl

def ExecutionReportReplaced.decode (tokens : List Token) : Option ExecutionReportReplaced := do
  let origClOrdID ← readRequired [52, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let ordType ← readRequired [52, 48] tokens
  pure { origClOrdID, optionsSecurityID, ordType }

theorem ExecutionReportReplaced.decode_agrees (record : ExecutionReportReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplaced.decode tokens = some record := by
  have distinct : ExecutionReportReplaced.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportReplaced.decode, origClOrdID, optionsSecurityID, ordType, some_bind] <;> rfl

structure ExecutionReportPendingCancel where
  origClOrdID : Terminated 1  -- tag 41
  optionsSecurityID : Option (Terminated 1)  -- tag 21035

def ExecutionReportPendingCancel.parts (record : ExecutionReportPendingCancel) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID]

def ExecutionReportPendingCancel.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[50, 49, 48, 51, 53]]]

theorem ExecutionReportPendingCancel.shape (record : ExecutionReportPendingCancel) : record.parts.map Part.tags = ExecutionReportPendingCancel.tags := rfl

def ExecutionReportPendingCancel.decode (tokens : List Token) : Option ExecutionReportPendingCancel := do
  let origClOrdID ← readRequired [52, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  pure { origClOrdID, optionsSecurityID }

theorem ExecutionReportPendingCancel.decode_agrees (record : ExecutionReportPendingCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPendingCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPendingCancel.decode tokens = some record := by
  have distinct : ExecutionReportPendingCancel.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportPendingCancel.decode, origClOrdID, optionsSecurityID, some_bind] <;> rfl

structure ExecutionReportCanceled where
  origClOrdID : Terminated 1  -- tag 41
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  cancelReason : Terminated 1  -- tag 21004

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [50, 49, 48, 48, 52] record.cancelReason]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[50, 49, 48, 51, 53]], [[50, 49, 48, 48, 52]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let origClOrdID ← readRequired [52, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let cancelReason ← readRequired [50, 49, 48, 48, 52] tokens
  pure { origClOrdID, optionsSecurityID, cancelReason }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cancelReason := readRequired_part [50, 49, 48, 48, 52] record.cancelReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, origClOrdID, optionsSecurityID, cancelReason, some_bind] <;> rfl

structure ExecutionReportExpired where
  origClOrdID : Terminated 1  -- tag 41
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  cancelReason : Terminated 1  -- tag 21004

def ExecutionReportExpired.parts (record : ExecutionReportExpired) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [50, 49, 48, 48, 52] record.cancelReason]

def ExecutionReportExpired.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[50, 49, 48, 51, 53]], [[50, 49, 48, 48, 52]]]

theorem ExecutionReportExpired.shape (record : ExecutionReportExpired) : record.parts.map Part.tags = ExecutionReportExpired.tags := rfl

def ExecutionReportExpired.decode (tokens : List Token) : Option ExecutionReportExpired := do
  let origClOrdID ← readRequired [52, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let cancelReason ← readRequired [50, 49, 48, 48, 52] tokens
  pure { origClOrdID, optionsSecurityID, cancelReason }

theorem ExecutionReportExpired.decode_agrees (record : ExecutionReportExpired) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportExpired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportExpired.decode tokens = some record := by
  have distinct : ExecutionReportExpired.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cancelReason := readRequired_part [50, 49, 48, 48, 52] record.cancelReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportExpired.decode, origClOrdID, optionsSecurityID, cancelReason, some_bind] <;> rfl

structure ExecutionReportRestated where
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  lastPx : Terminated 1  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  execRestatementReason : Terminated 1  -- tag 378
  extendedRestatementReason : Option (Terminated 1)  -- tag 21022

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55, 56] record.execRestatementReason,
   Part.optional [50, 49, 48, 50, 50] record.extendedRestatementReason]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 51, 53]], [[51, 49]], [[51, 50]], [[51, 55, 56]], [[50, 49, 48, 50, 50]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let execRestatementReason ← readRequired [51, 55, 56] tokens
  let extendedRestatementReason ← readOptional [50, 49, 48, 50, 50] tokens
  pure { optionsSecurityID, lastPx, lastQty, execRestatementReason, extendedRestatementReason }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execRestatementReason := readRequired_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have extendedRestatementReason := readOptional_part [50, 49, 48, 50, 50] record.extendedRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, optionsSecurityID, lastPx, lastQty, execRestatementReason, extendedRestatementReason, some_bind] <;> rfl

structure ExecutionReportTradeCorrect where
  execRefID : Terminated 1  -- tag 19
  optionsSecurityID : Terminated 1  -- tag 21035
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  avgPx : Terminated 1  -- tag 6
  trdMatchID : Terminated 1  -- tag 880

def ExecutionReportTradeCorrect.parts (record : ExecutionReportTradeCorrect) : List Part :=
  [Part.required [49, 57] record.execRefID,
   Part.required [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [54] record.avgPx,
   Part.required [56, 56, 48] record.trdMatchID]

def ExecutionReportTradeCorrect.tags : List (List (List UInt8)) :=
  [[[49, 57]], [[50, 49, 48, 51, 53]], [[51, 49]], [[51, 50]], [[54]], [[56, 56, 48]]]

theorem ExecutionReportTradeCorrect.shape (record : ExecutionReportTradeCorrect) : record.parts.map Part.tags = ExecutionReportTradeCorrect.tags := rfl

def ExecutionReportTradeCorrect.decode (tokens : List Token) : Option ExecutionReportTradeCorrect := do
  let execRefID ← readRequired [49, 57] tokens
  let optionsSecurityID ← readRequired [50, 49, 48, 51, 53] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let avgPx ← readRequired [54] tokens
  let trdMatchID ← readRequired [56, 56, 48] tokens
  pure { execRefID, optionsSecurityID, lastPx, lastQty, avgPx, trdMatchID }

theorem ExecutionReportTradeCorrect.decode_agrees (record : ExecutionReportTradeCorrect) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradeCorrect.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradeCorrect.decode tokens = some record := by
  have distinct : ExecutionReportTradeCorrect.tags.flatten.Nodup := by decide +kernel
  have execRefID := readRequired_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readRequired_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportTradeCorrect.decode, execRefID, optionsSecurityID, lastPx, lastQty, avgPx, trdMatchID, some_bind] <;> rfl

structure ExecutionReportTradeCancel where
  execRefID : Terminated 1  -- tag 19
  optionsSecurityID : Terminated 1  -- tag 21035
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  avgPx : Terminated 1  -- tag 6
  trdMatchID : Terminated 1  -- tag 880

def ExecutionReportTradeCancel.parts (record : ExecutionReportTradeCancel) : List Part :=
  [Part.required [49, 57] record.execRefID,
   Part.required [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [54] record.avgPx,
   Part.required [56, 56, 48] record.trdMatchID]

def ExecutionReportTradeCancel.tags : List (List (List UInt8)) :=
  [[[49, 57]], [[50, 49, 48, 51, 53]], [[51, 49]], [[51, 50]], [[54]], [[56, 56, 48]]]

theorem ExecutionReportTradeCancel.shape (record : ExecutionReportTradeCancel) : record.parts.map Part.tags = ExecutionReportTradeCancel.tags := rfl

def ExecutionReportTradeCancel.decode (tokens : List Token) : Option ExecutionReportTradeCancel := do
  let execRefID ← readRequired [49, 57] tokens
  let optionsSecurityID ← readRequired [50, 49, 48, 51, 53] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let avgPx ← readRequired [54] tokens
  let trdMatchID ← readRequired [56, 56, 48] tokens
  pure { execRefID, optionsSecurityID, lastPx, lastQty, avgPx, trdMatchID }

theorem ExecutionReportTradeCancel.decode_agrees (record : ExecutionReportTradeCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradeCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradeCancel.decode tokens = some record := by
  have distinct : ExecutionReportTradeCancel.tags.flatten.Nodup := by decide +kernel
  have execRefID := readRequired_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readRequired_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportTradeCancel.decode, execRefID, optionsSecurityID, lastPx, lastQty, avgPx, trdMatchID, some_bind] <;> rfl

structure UserNotification where
  userStatus : Terminated 1  -- tag 926

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.required [57, 50, 54] record.userStatus]

def UserNotification.tags : List (List (List UInt8)) :=
  [[[57, 50, 54]]]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let userStatus ← readRequired [57, 50, 54] tokens
  pure { userStatus }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [UserNotification.decode, userStatus, some_bind] <;> rfl

structure NoNestedPartyIDs where
  nestedPartyID : Terminated 1  -- tag 524
  nestedPartyIDSource : Terminated 1  -- tag 525
  nestedPartyRole : Terminated 1  -- tag 538

def NoNestedPartyIDs.parts (record : NoNestedPartyIDs) : List Part :=
  [Part.required [53, 50, 52] record.nestedPartyID,
   Part.required [53, 50, 53] record.nestedPartyIDSource,
   Part.required [53, 51, 56] record.nestedPartyRole]

def NoNestedPartyIDs.tags : List (List (List UInt8)) :=
  [[[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]]]

theorem NoNestedPartyIDs.shape (record : NoNestedPartyIDs) : record.parts.map Part.tags = NoNestedPartyIDs.tags := rfl

def NoNestedPartyIDs.decode (tokens : List Token) : Option NoNestedPartyIDs := do
  let nestedPartyID ← readRequired [53, 50, 52] tokens
  let nestedPartyIDSource ← readRequired [53, 50, 53] tokens
  let nestedPartyRole ← readRequired [53, 51, 56] tokens
  pure { nestedPartyID, nestedPartyIDSource, nestedPartyRole }

theorem NoNestedPartyIDs.decode_agrees (record : NoNestedPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoNestedPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoNestedPartyIDs.decode tokens = some record := by
  have distinct : NoNestedPartyIDs.tags.flatten.Nodup := by decide +kernel
  have nestedPartyID := readRequired_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have nestedPartyIDSource := readRequired_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nestedPartyRole := readRequired_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoNestedPartyIDs.decode, nestedPartyID, nestedPartyIDSource, nestedPartyRole, some_bind] <;> rfl

def NoNestedPartyIDs.members : List (List UInt8) := NoNestedPartyIDs.tags.flatten

def NoNestedPartyIDs.encode (entry : NoNestedPartyIDs) : List Token := encodeParts entry.parts

theorem NoNestedPartyIDs.decode_encode (entry : NoNestedPartyIDs) : NoNestedPartyIDs.decode entry.encode = some entry :=
  NoNestedPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoNestedPartyIDs.within (entry : NoNestedPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoNestedPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoNestedPartyIDs.shape] at this

theorem NoNestedPartyIDs.led (entry : NoNestedPartyIDs) : Lead [53, 50, 52] entry.encode :=
  lead_parts [53, 50, 52] entry.nestedPartyID _ NoNestedPartyIDs.tags.tail rfl (by decide +kernel)

structure NoAllocs where
  allocQty : Terminated 1  -- tag 80
  allocPositionEffect : Option (Terminated 1)  -- tag 1047
  tradingCapacity : Terminated 1  -- tag 1815
  individualAllocID : Terminated 1  -- tag 467
  noNestedPartyIDs : List NoNestedPartyIDs  -- tag 539

def NoAllocs.parts (record : NoAllocs) : List Part :=
  [Part.required [56, 48] record.allocQty,
   Part.optional [49, 48, 52, 55] record.allocPositionEffect,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.required [52, 54, 55] record.individualAllocID,
   Part.group [53, 51, 57] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within record.noNestedPartyIDs]

def NoAllocs.tags : List (List (List UInt8)) :=
  [[[56, 48]], [[49, 48, 52, 55]], [[49, 56, 49, 53]], [[52, 54, 55]], [53, 51, 57] :: NoNestedPartyIDs.members]

theorem NoAllocs.shape (record : NoAllocs) : record.parts.map Part.tags = NoAllocs.tags := rfl

def NoAllocs.decode (tokens : List Token) : Option NoAllocs := do
  let allocQty ← readRequired [56, 48] tokens
  let allocPositionEffect ← readOptional [49, 48, 52, 55] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let individualAllocID ← readRequired [52, 54, 55] tokens
  let noNestedPartyIDs ← readGroup [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.decode tokens
  pure { allocQty, allocPositionEffect, tradingCapacity, individualAllocID, noNestedPartyIDs }

theorem NoAllocs.decode_agrees (record : NoAllocs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocs.decode tokens = some record := by
  have distinct : NoAllocs.tags.flatten.Nodup := by decide +kernel
  have allocQty := readRequired_part [56, 48] record.allocQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocPositionEffect := readOptional_part [49, 48, 52, 55] record.allocPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have individualAllocID := readRequired_part [52, 54, 55] record.individualAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noNestedPartyIDs := readGroup_part [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within NoNestedPartyIDs.decode NoNestedPartyIDs.decode_encode NoNestedPartyIDs.led record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoAllocs.decode, allocQty, allocPositionEffect, tradingCapacity, individualAllocID, noNestedPartyIDs, some_bind] <;> rfl

def NoAllocs.members : List (List UInt8) := NoAllocs.tags.flatten

def NoAllocs.encode (entry : NoAllocs) : List Token := encodeParts entry.parts

theorem NoAllocs.decode_encode (entry : NoAllocs) : NoAllocs.decode entry.encode = some entry :=
  NoAllocs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAllocs.within (entry : NoAllocs) : ∀ token ∈ entry.encode, token.tag ∈ NoAllocs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAllocs.shape] at this

theorem NoAllocs.led (entry : NoAllocs) : Lead [56, 48] entry.encode :=
  lead_parts [56, 48] entry.allocQty _ NoAllocs.tags.tail rfl (by decide +kernel)

structure AllocationInstructionAck where
  allocID : Terminated 1  -- tag 70
  allocType : Terminated 1  -- tag 626
  allocTransType : Terminated 1  -- tag 71
  secondaryAllocID : Terminated 1  -- tag 793
  refAllocID : Option (Terminated 1)  -- tag 72
  allocStatus : Terminated 1  -- tag 87
  allocRejCode : Option (Terminated 1)  -- tag 88
  noAllocs : List NoAllocs  -- tag 78

def AllocationInstructionAck.parts (record : AllocationInstructionAck) : List Part :=
  [Part.required [55, 48] record.allocID,
   Part.required [54, 50, 54] record.allocType,
   Part.required [55, 49] record.allocTransType,
   Part.required [55, 57, 51] record.secondaryAllocID,
   Part.optional [55, 50] record.refAllocID,
   Part.required [56, 55] record.allocStatus,
   Part.optional [56, 56] record.allocRejCode,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs]

def AllocationInstructionAck.tags : List (List (List UInt8)) :=
  [[[55, 48]], [[54, 50, 54]], [[55, 49]], [[55, 57, 51]], [[55, 50]], [[56, 55]], [[56, 56]], [55, 56] :: NoAllocs.members]

theorem AllocationInstructionAck.shape (record : AllocationInstructionAck) : record.parts.map Part.tags = AllocationInstructionAck.tags := rfl

def AllocationInstructionAck.decode (tokens : List Token) : Option AllocationInstructionAck := do
  let allocID ← readRequired [55, 48] tokens
  let allocType ← readRequired [54, 50, 54] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let secondaryAllocID ← readRequired [55, 57, 51] tokens
  let refAllocID ← readOptional [55, 50] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let allocRejCode ← readOptional [56, 56] tokens
  let noAllocs ← readGroup [55, 56] [56, 48] NoAllocs.members NoAllocs.decode tokens
  pure { allocID, allocType, allocTransType, secondaryAllocID, refAllocID, allocStatus, allocRejCode, noAllocs }

theorem AllocationInstructionAck.decode_agrees (record : AllocationInstructionAck) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationInstructionAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationInstructionAck.decode tokens = some record := by
  have distinct : AllocationInstructionAck.tags.flatten.Nodup := by decide +kernel
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocType := readRequired_part [54, 50, 54] record.allocType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have secondaryAllocID := readRequired_part [55, 57, 51] record.secondaryAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have refAllocID := readOptional_part [55, 50] record.refAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have allocRejCode := readOptional_part [56, 56] record.allocRejCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [56, 48] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [AllocationInstructionAck.decode, allocID, allocType, allocTransType, secondaryAllocID, refAllocID, allocStatus, allocRejCode, noAllocs, some_bind] <;> rfl

structure NoExecs where
  tradeId : Terminated 1  -- tag 1003
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31

def NoExecs.parts (record : NoExecs) : List Part :=
  [Part.required [49, 48, 48, 51] record.tradeId,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx]

def NoExecs.tags : List (List (List UInt8)) :=
  [[[49, 48, 48, 51]], [[51, 50]], [[51, 49]]]

theorem NoExecs.shape (record : NoExecs) : record.parts.map Part.tags = NoExecs.tags := rfl

def NoExecs.decode (tokens : List Token) : Option NoExecs := do
  let tradeId ← readRequired [49, 48, 48, 51] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  pure { tradeId, lastQty, lastPx }

theorem NoExecs.decode_agrees (record : NoExecs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoExecs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoExecs.decode tokens = some record := by
  have distinct : NoExecs.tags.flatten.Nodup := by decide +kernel
  have tradeId := readRequired_part [49, 48, 48, 51] record.tradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoExecs.decode, tradeId, lastQty, lastPx, some_bind] <;> rfl

def NoExecs.members : List (List UInt8) := NoExecs.tags.flatten

def NoExecs.encode (entry : NoExecs) : List Token := encodeParts entry.parts

theorem NoExecs.decode_encode (entry : NoExecs) : NoExecs.decode entry.encode = some entry :=
  NoExecs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoExecs.within (entry : NoExecs) : ∀ token ∈ entry.encode, token.tag ∈ NoExecs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoExecs.shape] at this

theorem NoExecs.led (entry : NoExecs) : Lead [49, 48, 48, 51] entry.encode :=
  lead_parts [49, 48, 48, 51] entry.tradeId _ NoExecs.tags.tail rfl (by decide +kernel)

structure AllocationInstructionAlert where
  allocID : Terminated 1  -- tag 70
  allocType : Terminated 1  -- tag 626
  allocTransType : Terminated 1  -- tag 71
  refAllocID : Option (Terminated 1)  -- tag 72
  allocCancReplaceReason : Option (Terminated 1)  -- tag 796
  side : Terminated 1  -- tag 54
  optionsSecurityID : Terminated 1  -- tag 21035
  symbol : Terminated 1  -- tag 55
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  tradeDate : Terminated 1  -- tag 75
  noExecs : List NoExecs  -- tag 124
  noAllocs : List NoAllocs  -- tag 78

def AllocationInstructionAlert.parts (record : AllocationInstructionAlert) : List Part :=
  [Part.required [55, 48] record.allocID,
   Part.required [54, 50, 54] record.allocType,
   Part.required [55, 49] record.allocTransType,
   Part.optional [55, 50] record.refAllocID,
   Part.optional [55, 57, 54] record.allocCancReplaceReason,
   Part.required [53, 52] record.side,
   Part.required [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [55, 53] record.tradeDate,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs]

def AllocationInstructionAlert.tags : List (List (List UInt8)) :=
  [[[55, 48]], [[54, 50, 54]], [[55, 49]], [[55, 50]], [[55, 57, 54]], [[53, 52]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[55, 53]], [49, 50, 52] :: NoExecs.members, [55, 56] :: NoAllocs.members]

theorem AllocationInstructionAlert.shape (record : AllocationInstructionAlert) : record.parts.map Part.tags = AllocationInstructionAlert.tags := rfl

def AllocationInstructionAlert.decode (tokens : List Token) : Option AllocationInstructionAlert := do
  let allocID ← readRequired [55, 48] tokens
  let allocType ← readRequired [54, 50, 54] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let refAllocID ← readOptional [55, 50] tokens
  let allocCancReplaceReason ← readOptional [55, 57, 54] tokens
  let side ← readRequired [53, 52] tokens
  let optionsSecurityID ← readRequired [50, 49, 48, 51, 53] tokens
  let symbol ← readRequired [53, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let noExecs ← readGroup [49, 50, 52] [49, 48, 48, 51] NoExecs.members NoExecs.decode tokens
  let noAllocs ← readGroup [55, 56] [56, 48] NoAllocs.members NoAllocs.decode tokens
  pure { allocID, allocType, allocTransType, refAllocID, allocCancReplaceReason, side, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, tradeDate, noExecs, noAllocs }

theorem AllocationInstructionAlert.decode_agrees (record : AllocationInstructionAlert) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationInstructionAlert.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationInstructionAlert.decode tokens = some record := by
  have distinct : AllocationInstructionAlert.tags.flatten.Nodup := by decide +kernel
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocType := readRequired_part [54, 50, 54] record.allocType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refAllocID := readOptional_part [55, 50] record.refAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocCancReplaceReason := readOptional_part [55, 57, 54] record.allocCancReplaceReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have optionsSecurityID := readRequired_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [49, 48, 48, 51] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [56, 48] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [AllocationInstructionAlert.decode, allocID, allocType, allocTransType, refAllocID, allocCancReplaceReason, side, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, tradeDate, noExecs, noAllocs, some_bind] <;> rfl

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade)
  | executionReportPendingReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingReplace)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportPendingCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingCancel)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportTradeCorrect (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCorrect)
  | executionReportTradeCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCancel)
  | userNotification (header : Header) (r0 : UserNotification)
  | allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck)
  | allocationInstructionAlert (header : Header) (r0 : AllocationInstructionAlert)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportTrade header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .executionReportPendingReplace header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportPendingCancel header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportExpired header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportTradeCorrect header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts)
  | .executionReportTradeCancel header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts)
  | .userNotification header r0 => ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationInstructionAck header r0 => ⟨[51, 53], ⟨[80], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationInstructionAlert header r0 => ⟨[51, 53], ⟨[66, 77], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
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
          else if key.val = [70] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTrade.decode rest
              pure (.executionReportTrade header r0 r1)
            else none
          else if key.val = [69] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPendingReplace.decode rest
              pure (.executionReportPendingReplace header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportReplaced.decode rest
              pure (.executionReportReplaced header r0 r1)
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
          else if key.val = [67] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportExpired.decode rest
              pure (.executionReportExpired header r0 r1)
            else none
          else if key.val = [68] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRestated.decode rest
              pure (.executionReportRestated header r0 r1)
            else none
          else if key.val = [71] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCorrect.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradeCorrect.decode rest
              pure (.executionReportTradeCorrect header r0 r1)
            else none
          else if key.val = [72] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCancel.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradeCancel.decode rest
              pure (.executionReportTradeCancel header r0 r1)
            else none
          else none
      else if token.value.val = [67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
        else none
      else if token.value.val = [80] then
        if known (Header.tags ++ AllocationInstructionAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationInstructionAck.decode rest
          pure (.allocationInstructionAck header r0)
        else none
      else if token.value.val = [66, 77] then
        if known (Header.tags ++ AllocationInstructionAlert.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationInstructionAlert.decode rest
          pure (.allocationInstructionAlert header r0)
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

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
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

theorem Message.decode_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decode (Message.tokens (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[70], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl
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

theorem Message.decode_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decode (Message.tokens (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportReplaced.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportReplaced.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportReplaced.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl
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

theorem Message.decode_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decode (Message.tokens (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportExpired.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportExpired.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportExpired.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl
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

theorem Message.decode_executionReportTradeCorrect (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCorrect) :
    Message.decode (Message.tokens (.executionReportTradeCorrect header r0 r1)) = some (.executionReportTradeCorrect header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCorrect.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradeCorrect.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[71], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[71], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradeCorrect.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradeCorrect.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradeCorrect.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCorrect.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradeCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCancel) :
    Message.decode (Message.tokens (.executionReportTradeCancel header r0 r1)) = some (.executionReportTradeCancel header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCancel.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradeCancel.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[72], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[72], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradeCancel.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradeCancel.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradeCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCancel.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck) :
    Message.decode (Message.tokens (.allocationInstructionAck header r0)) = some (.allocationInstructionAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAck.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationInstructionAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationInstructionAlert (header : Header) (r0 : AllocationInstructionAlert) :
    Message.decode (Message.tokens (.allocationInstructionAlert header r0)) = some (.allocationInstructionAlert header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAlert.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationInstructionAlert.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstructionAlert.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAlert.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decode_executionReportTrade header r0 r1
  | executionReportPendingReplace header r0 r1 => exact Message.decode_executionReportPendingReplace header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportPendingCancel header r0 r1 => exact Message.decode_executionReportPendingCancel header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decode_executionReportExpired header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportTradeCorrect header r0 r1 => exact Message.decode_executionReportTradeCorrect header r0 r1
  | executionReportTradeCancel header r0 r1 => exact Message.decode_executionReportTradeCancel header r0 r1
  | userNotification header r0 => exact Message.decode_userNotification header r0
  | allocationInstructionAck header r0 => exact Message.decode_allocationInstructionAck header r0
  | allocationInstructionAlert header r0 => exact Message.decode_allocationInstructionAlert header r0

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

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

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

theorem Message.decodeBytes_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decodeBytes (Message.encode (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTrade header r0 r1

theorem Message.decodeBytes_executionReportPendingReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingReplace) :
    Message.decodeBytes (Message.encode (.executionReportPendingReplace header r0 r1)) = some (.executionReportPendingReplace header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[69], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingReplace.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPendingReplace header r0 r1

theorem Message.decodeBytes_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decodeBytes (Message.encode (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplaced header r0 r1

theorem Message.decodeBytes_executionReportPendingCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPendingCancel) :
    Message.decodeBytes (Message.encode (.executionReportPendingCancel header r0 r1)) = some (.executionReportPendingCancel header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[54], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPendingCancel.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPendingCancel header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decodeBytes (Message.encode (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportExpired header r0 r1

theorem Message.decodeBytes_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decodeBytes (Message.encode (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRestated header r0 r1

theorem Message.decodeBytes_executionReportTradeCorrect (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCorrect) :
    Message.decodeBytes (Message.encode (.executionReportTradeCorrect header r0 r1)) = some (.executionReportTradeCorrect header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[71], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCorrect.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradeCorrect header r0 r1

theorem Message.decodeBytes_executionReportTradeCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradeCancel) :
    Message.decodeBytes (Message.encode (.executionReportTradeCancel header r0 r1)) = some (.executionReportTradeCancel header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradeCancel.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradeCancel header r0 r1

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_allocationInstructionAck (header : Header) (r0 : AllocationInstructionAck) :
    Message.decodeBytes (Message.encode (.allocationInstructionAck header r0)) = some (.allocationInstructionAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[80], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationInstructionAck header r0

theorem Message.decodeBytes_allocationInstructionAlert (header : Header) (r0 : AllocationInstructionAlert) :
    Message.decodeBytes (Message.encode (.allocationInstructionAlert header r0)) = some (.allocationInstructionAlert header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 77], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationInstructionAlert.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationInstructionAlert header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decodeBytes_executionReportTrade header r0 r1
  | executionReportPendingReplace header r0 r1 => exact Message.decodeBytes_executionReportPendingReplace header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportPendingCancel header r0 r1 => exact Message.decodeBytes_executionReportPendingCancel header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decodeBytes_executionReportExpired header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportTradeCorrect header r0 r1 => exact Message.decodeBytes_executionReportTradeCorrect header r0 r1
  | executionReportTradeCancel header r0 r1 => exact Message.decodeBytes_executionReportTradeCancel header r0 r1
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0
  | allocationInstructionAck header r0 => exact Message.decodeBytes_allocationInstructionAck header r0
  | allocationInstructionAlert header r0 => exact Message.decodeBytes_allocationInstructionAlert header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.MemxMemxoptionsOrderentryFixV110Exchange
