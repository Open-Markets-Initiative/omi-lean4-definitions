import Wire

/-!
# Box Options Market Order Entry v4.5, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.BoxBoxoptionsOrderentryFixV45Client

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

structure NewSingleComplexOrder where
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  account : Option (Terminated 1)  -- tag 1
  securityType : Terminated 1  -- tag 167
  symbol : Terminated 1  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  side : Terminated 1  -- tag 54
  transactTime : Option (Terminated 1)  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Terminated 1  -- tag 40
  rule80A : Terminated 1  -- tag 47
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  text : Option (Terminated 1)  -- tag 58
  openClose : Terminated 1  -- tag 77
  execBroker : Option (Terminated 1)  -- tag 76
  clearingFirm : Option (Terminated 1)  -- tag 439
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  combinedOrdType : Option (Terminated 1)  -- tag 7906
  routingInst : Option (Terminated 1)  -- tag 9303

def NewSingleComplexOrder.parts (record : NewSingleComplexOrder) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49] record.account,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.required [53, 52] record.side,
   Part.optional [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 55] record.rule80A,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 56] record.text,
   Part.required [55, 55] record.openClose,
   Part.optional [55, 54] record.execBroker,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [55, 57, 48, 54] record.combinedOrdType,
   Part.optional [57, 51, 48, 51] record.routingInst]

def NewSingleComplexOrder.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 56]], [[49]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 55]], [[52, 52]], [[53, 57]], [[52, 51, 50]], [[53, 56]], [[55, 55]], [[55, 54]], [[52, 51, 57]], [[55, 57, 48, 49]], [[55, 57, 48, 54]], [[57, 51, 48, 51]]]

theorem NewSingleComplexOrder.shape (record : NewSingleComplexOrder) : record.parts.map Part.tags = NewSingleComplexOrder.tags := rfl

def NewSingleComplexOrder.decode (tokens : List Token) : Option NewSingleComplexOrder := do
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let account ← readOptional [49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let rule80A ← readRequired [52, 55] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let text ← readOptional [53, 56] tokens
  let openClose ← readRequired [55, 55] tokens
  let execBroker ← readOptional [55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let combinedOrdType ← readOptional [55, 57, 48, 54] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  pure { clOrdID, execInst, account, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, expireDate, text, openClose, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst }

theorem NewSingleComplexOrder.decode_agrees (record : NewSingleComplexOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ NewSingleComplexOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewSingleComplexOrder.decode tokens = some record := by
  have distinct : NewSingleComplexOrder.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have rule80A := readRequired_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have combinedOrdType := readOptional_part [55, 57, 48, 54] record.combinedOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  simp only [NewSingleComplexOrder.decode, clOrdID, execInst, account, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, expireDate, text, openClose, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst, some_bind] <;> rfl

structure CancelReplaceSingleComplexOrderRequestOrder where
  orderID : Option (Terminated 1)  -- tag 37
  account : Option (Terminated 1)  -- tag 1
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  securityType : Terminated 1  -- tag 167
  symbol : Terminated 1  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  rule80A : Option (Terminated 1)  -- tag 47
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  text : Option (Terminated 1)  -- tag 58
  openClose : Option (Terminated 1)  -- tag 77
  execBroker : Option (Terminated 1)  -- tag 76
  clearingFirm : Option (Terminated 1)  -- tag 439
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  combinedOrdType : Option (Terminated 1)  -- tag 7906
  routingInst : Option (Terminated 1)  -- tag 9303

def CancelReplaceSingleComplexOrderRequestOrder.parts (record : CancelReplaceSingleComplexOrderRequestOrder) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.optional [49] record.account,
   Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 55] record.rule80A,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 56] record.text,
   Part.optional [55, 55] record.openClose,
   Part.optional [55, 54] record.execBroker,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [55, 57, 48, 54] record.combinedOrdType,
   Part.optional [57, 51, 48, 51] record.routingInst]

def CancelReplaceSingleComplexOrderRequestOrder.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49]], [[52, 49]], [[49, 49]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 55]], [[52, 52]], [[53, 57]], [[52, 51, 50]], [[53, 56]], [[55, 55]], [[55, 54]], [[52, 51, 57]], [[55, 57, 48, 49]], [[55, 57, 48, 54]], [[57, 51, 48, 51]]]

theorem CancelReplaceSingleComplexOrderRequestOrder.shape (record : CancelReplaceSingleComplexOrderRequestOrder) : record.parts.map Part.tags = CancelReplaceSingleComplexOrderRequestOrder.tags := rfl

def CancelReplaceSingleComplexOrderRequestOrder.decode (tokens : List Token) : Option CancelReplaceSingleComplexOrderRequestOrder := do
  let orderID ← readOptional [51, 55] tokens
  let account ← readOptional [49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let rule80A ← readOptional [52, 55] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let text ← readOptional [53, 56] tokens
  let openClose ← readOptional [55, 55] tokens
  let execBroker ← readOptional [55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let combinedOrdType ← readOptional [55, 57, 48, 54] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  pure { orderID, account, origClOrdID, clOrdID, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, expireDate, text, openClose, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst }

theorem CancelReplaceSingleComplexOrderRequestOrder.decode_agrees (record : CancelReplaceSingleComplexOrderRequestOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelReplaceSingleComplexOrderRequestOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelReplaceSingleComplexOrderRequestOrder.decode tokens = some record := by
  have distinct : CancelReplaceSingleComplexOrderRequestOrder.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have combinedOrdType := readOptional_part [55, 57, 48, 54] record.combinedOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [CancelReplaceSingleComplexOrderRequestOrder.decode, orderID, account, origClOrdID, clOrdID, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, expireDate, text, openClose, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst, some_bind] <;> rfl

structure AuctionInitialOrder where
  securityType : Terminated 1  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  price : Terminated 1  -- tag 44
  qtyType : Option (Terminated 1)  -- tag 854
  priceImprovement : Option (Terminated 1)  -- tag 639
  improvePhaseID : Option (Terminated 1)  -- tag 7900
  addQty : Option (Terminated 1)  -- tag 9461
  auctionType : Option (Terminated 1)  -- tag 9383
  contingentOrder : Option (Terminated 1)  -- tag 7388
  noClearingData : Terminated 1  -- tag 7904
  noLegs : Terminated 1  -- tag 555

def AuctionInitialOrder.parts (record : AuctionInitialOrder) : List Part :=
  [Part.required [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 52] record.price,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [54, 51, 57] record.priceImprovement,
   Part.optional [55, 57, 48, 48] record.improvePhaseID,
   Part.optional [57, 52, 54, 49] record.addQty,
   Part.optional [57, 51, 56, 51] record.auctionType,
   Part.optional [55, 51, 56, 56] record.contingentOrder,
   Part.required [55, 57, 48, 52] record.noClearingData,
   Part.required [53, 53, 53] record.noLegs]

def AuctionInitialOrder.tags : List (List (List UInt8)) :=
  [[[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52]], [[51, 56]], [[52, 52]], [[56, 53, 52]], [[54, 51, 57]], [[55, 57, 48, 48]], [[57, 52, 54, 49]], [[57, 51, 56, 51]], [[55, 51, 56, 56]], [[55, 57, 48, 52]], [[53, 53, 53]]]

theorem AuctionInitialOrder.shape (record : AuctionInitialOrder) : record.parts.map Part.tags = AuctionInitialOrder.tags := rfl

def AuctionInitialOrder.decode (tokens : List Token) : Option AuctionInitialOrder := do
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let price ← readRequired [52, 52] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let priceImprovement ← readOptional [54, 51, 57] tokens
  let improvePhaseID ← readOptional [55, 57, 48, 48] tokens
  let addQty ← readOptional [57, 52, 54, 49] tokens
  let auctionType ← readOptional [57, 51, 56, 51] tokens
  let contingentOrder ← readOptional [55, 51, 56, 56] tokens
  let noClearingData ← readRequired [55, 57, 48, 52] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  pure { securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, orderQty, price, qtyType, priceImprovement, improvePhaseID, addQty, auctionType, contingentOrder, noClearingData, noLegs }

theorem AuctionInitialOrder.decode_agrees (record : AuctionInitialOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ AuctionInitialOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AuctionInitialOrder.decode tokens = some record := by
  have distinct : AuctionInitialOrder.tags.flatten.Nodup := by decide +kernel
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have priceImprovement := readOptional_part [54, 51, 57] record.priceImprovement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have improvePhaseID := readOptional_part [55, 57, 48, 48] record.improvePhaseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have addQty := readOptional_part [57, 52, 54, 49] record.addQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 56, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have contingentOrder := readOptional_part [55, 51, 56, 56] record.contingentOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noClearingData := readRequired_part [55, 57, 48, 52] record.noClearingData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [AuctionInitialOrder.decode, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, orderQty, price, qtyType, priceImprovement, improvePhaseID, addQty, auctionType, contingentOrder, noClearingData, noLegs, some_bind] <;> rfl

structure OrderSingleComplexCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  orderQty : Option (Terminated 1)  -- tag 38
  securityType : Terminated 1  -- tag 167
  symbol : Terminated 1  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  side : Terminated 1  -- tag 54
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  noLegs : Option (Terminated 1)  -- tag 555

def OrderSingleComplexCancelRequest.parts (record : OrderSingleComplexCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [51, 56] record.orderQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.required [53, 52] record.side,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 53, 53] record.noLegs]

def OrderSingleComplexCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[51, 55]], [[49, 49]], [[51, 56]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52]], [[53, 56]], [[54, 48]], [[53, 53, 53]]]

theorem OrderSingleComplexCancelRequest.shape (record : OrderSingleComplexCancelRequest) : record.parts.map Part.tags = OrderSingleComplexCancelRequest.tags := rfl

def OrderSingleComplexCancelRequest.decode (tokens : List Token) : Option OrderSingleComplexCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readOptional [51, 56] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let side ← readRequired [53, 52] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let noLegs ← readOptional [53, 53, 53] tokens
  pure { origClOrdID, orderID, clOrdID, orderQty, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, text, transactTime, noLegs }

theorem OrderSingleComplexCancelRequest.decode_agrees (record : OrderSingleComplexCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderSingleComplexCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderSingleComplexCancelRequest.decode tokens = some record := by
  have distinct : OrderSingleComplexCancelRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noLegs := readOptional_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [OrderSingleComplexCancelRequest.decode, origClOrdID, orderID, clOrdID, orderQty, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, side, text, transactTime, noLegs, some_bind] <;> rfl

structure QuoteRequest where
  quoteReqID : Option (Terminated 1)  -- tag 131
  noRelatedSym : Option (Terminated 1)  -- tag 146
  securityType : Terminated 1  -- tag 167
  symbol : Terminated 1  -- tag 55
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityMonthYear : Terminated 1  -- tag 200
  maturityDay : Terminated 1  -- tag 205
  orderQty : Option (Terminated 1)  -- tag 38

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [49, 52, 54] record.noRelatedSym,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 53] record.symbol,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 53] record.maturityDay,
   Part.optional [51, 56] record.orderQty]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[49, 52, 54]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 48]], [[50, 48, 53]], [[51, 56]]]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let noRelatedSym ← readOptional [49, 52, 54] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let orderQty ← readOptional [51, 56] tokens
  pure { quoteReqID, noRelatedSym, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, orderQty }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRelatedSym := readOptional_part [49, 52, 54] record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, noRelatedSym, securityType, symbol, putOrCall, strikePrice, maturityMonthYear, maturityDay, orderQty, some_bind] <;> rfl

structure SecurityDefinitionRequest where
  securityReqID : Option (Terminated 1)  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  securityType : Option (Terminated 1)  -- tag 167
  noRelatedSym : Option (Terminated 1)  -- tag 146

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.optional [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [49, 52, 54] record.noRelatedSym]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[49, 54, 55]], [[49, 52, 54]]]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readOptional [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let noRelatedSym ← readOptional [49, 52, 54] tokens
  pure { securityReqID, securityRequestType, securityType, noRelatedSym }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readOptional_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noRelatedSym := readOptional_part [49, 52, 54] record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, securityType, noRelatedSym, some_bind] <;> rfl

structure OrderMassStatusRequest where
  massStatusReqID2 : Option (Terminated 1)  -- tag 584
  massStatusReqType : Option (Terminated 1)  -- tag 585

def OrderMassStatusRequest.parts (record : OrderMassStatusRequest) : List Part :=
  [Part.optional [53, 56, 52] record.massStatusReqID2,
   Part.optional [53, 56, 53] record.massStatusReqType]

def OrderMassStatusRequest.tags : List (List (List UInt8)) :=
  [[[53, 56, 52]], [[53, 56, 53]]]

theorem OrderMassStatusRequest.shape (record : OrderMassStatusRequest) : record.parts.map Part.tags = OrderMassStatusRequest.tags := rfl

def OrderMassStatusRequest.decode (tokens : List Token) : Option OrderMassStatusRequest := do
  let massStatusReqID2 ← readOptional [53, 56, 52] tokens
  let massStatusReqType ← readOptional [53, 56, 53] tokens
  pure { massStatusReqID2, massStatusReqType }

theorem OrderMassStatusRequest.decode_agrees (record : OrderMassStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassStatusRequest.decode tokens = some record := by
  have distinct : OrderMassStatusRequest.tags.flatten.Nodup := by decide +kernel
  have massStatusReqID2 := readOptional_part [53, 56, 52] record.massStatusReqID2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massStatusReqType := readOptional_part [53, 56, 53] record.massStatusReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [OrderMassStatusRequest.decode, massStatusReqID2, massStatusReqType, some_bind] <;> rfl

structure NewMultiLegOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  account : Option (Terminated 1)  -- tag 1
  securityType : Terminated 1  -- tag 167
  side : Terminated 1  -- tag 54
  transactTime : Option (Terminated 1)  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Terminated 1  -- tag 40
  rule80A : Terminated 1  -- tag 47
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  clearingFirm : Option (Terminated 1)  -- tag 439
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  combinedOrdType : Option (Terminated 1)  -- tag 7906
  routingInst : Option (Terminated 1)  -- tag 9303
  noLegs : Terminated 1  -- tag 555

def NewMultiLegOrderSingle.parts (record : NewMultiLegOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49] record.account,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 52] record.side,
   Part.optional [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 55] record.rule80A,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [55, 57, 48, 54] record.combinedOrdType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.required [53, 53, 53] record.noLegs]

def NewMultiLegOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49]], [[49, 54, 55]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 55]], [[52, 52]], [[53, 57]], [[53, 56]], [[55, 54]], [[52, 51, 57]], [[55, 57, 48, 49]], [[55, 57, 48, 54]], [[57, 51, 48, 51]], [[53, 53, 53]]]

theorem NewMultiLegOrderSingle.shape (record : NewMultiLegOrderSingle) : record.parts.map Part.tags = NewMultiLegOrderSingle.tags := rfl

def NewMultiLegOrderSingle.decode (tokens : List Token) : Option NewMultiLegOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let account ← readOptional [49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let rule80A ← readRequired [52, 55] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let combinedOrdType ← readOptional [55, 57, 48, 54] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  pure { clOrdID, account, securityType, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, text, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst, noLegs }

theorem NewMultiLegOrderSingle.decode_agrees (record : NewMultiLegOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewMultiLegOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewMultiLegOrderSingle.decode tokens = some record := by
  have distinct : NewMultiLegOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have rule80A := readRequired_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have combinedOrdType := readOptional_part [55, 57, 48, 54] record.combinedOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [NewMultiLegOrderSingle.decode, clOrdID, account, securityType, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, text, execBroker, clearingFirm, executingParticipantID, combinedOrdType, routingInst, noLegs, some_bind] <;> rfl

structure CancelReplaceMultiLegOrder where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  account : Option (Terminated 1)  -- tag 1
  securityType : Terminated 1  -- tag 167
  side : Terminated 1  -- tag 54
  transactTime : Option (Terminated 1)  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Terminated 1  -- tag 40
  rule80A : Option (Terminated 1)  -- tag 47
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  clearingFirm : Option (Terminated 1)  -- tag 439
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  routingInst : Option (Terminated 1)  -- tag 9303
  noLegs : Terminated 1  -- tag 555

def CancelReplaceMultiLegOrder.parts (record : CancelReplaceMultiLegOrder) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [49] record.account,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 52] record.side,
   Part.optional [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 55] record.rule80A,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.required [53, 53, 53] record.noLegs]

def CancelReplaceMultiLegOrder.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[49]], [[49, 54, 55]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 55]], [[52, 52]], [[53, 57]], [[53, 56]], [[55, 54]], [[52, 51, 57]], [[55, 57, 48, 49]], [[57, 51, 48, 51]], [[53, 53, 53]]]

theorem CancelReplaceMultiLegOrder.shape (record : CancelReplaceMultiLegOrder) : record.parts.map Part.tags = CancelReplaceMultiLegOrder.tags := rfl

def CancelReplaceMultiLegOrder.decode (tokens : List Token) : Option CancelReplaceMultiLegOrder := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let account ← readOptional [49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let rule80A ← readOptional [52, 55] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  pure { orderID, clOrdID, origClOrdID, account, securityType, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, text, execBroker, clearingFirm, executingParticipantID, routingInst, noLegs }

theorem CancelReplaceMultiLegOrder.decode_agrees (record : CancelReplaceMultiLegOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelReplaceMultiLegOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelReplaceMultiLegOrder.decode tokens = some record := by
  have distinct : CancelReplaceMultiLegOrder.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [CancelReplaceMultiLegOrder.decode, orderID, clOrdID, origClOrdID, account, securityType, side, transactTime, orderQty, ordType, rule80A, price, timeInForce, text, execBroker, clearingFirm, executingParticipantID, routingInst, noLegs, some_bind] <;> rfl

structure UserRequest where
  transactTime : Terminated 1  -- tag 60
  userRequestId : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924
  securityType : Option (Terminated 1)  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  putOrCall : Option (Terminated 1)  -- tag 201
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  strikePrice : Option (Terminated 1)  -- tag 202
  rule80A : Option (Terminated 1)  -- tag 47

def UserRequest.parts (record : UserRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [57, 50, 51] record.userRequestId,
   Part.required [57, 50, 52] record.userRequestType,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [52, 55] record.rule80A]

def UserRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[57, 50, 51]], [[57, 50, 52]], [[49, 54, 55]], [[53, 53]], [[50, 48, 49]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 50]], [[52, 55]]]

theorem UserRequest.shape (record : UserRequest) : record.parts.map Part.tags = UserRequest.tags := rfl

def UserRequest.decode (tokens : List Token) : Option UserRequest := do
  let transactTime ← readRequired [54, 48] tokens
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

theorem UserRequest.decode_agrees (record : UserRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserRequest.decode tokens = some record := by
  have distinct : UserRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
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
  simp only [UserRequest.decode, transactTime, userRequestId, userRequestType, securityType, symbol, putOrCall, maturityMonthYear, maturityDay, strikePrice, rule80A, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | fIXProtocolErrorReject (header : Header) (r0 : FIXProtocolErrorReject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | newSingleComplexOrder (header : Header) (r0 : NewSingleComplexOrder)
  | cancelReplaceSingleComplexOrderRequestOrder (header : Header) (r0 : CancelReplaceSingleComplexOrderRequestOrder)
  | auctionInitialOrder (header : Header) (r0 : AuctionInitialOrder)
  | orderSingleComplexCancelRequest (header : Header) (r0 : OrderSingleComplexCancelRequest)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest)
  | newMultiLegOrderSingle (header : Header) (r0 : NewMultiLegOrderSingle)
  | cancelReplaceMultiLegOrder (header : Header) (r0 : CancelReplaceMultiLegOrder)
  | userRequest (header : Header) (r0 : UserRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .fIXProtocolErrorReject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newSingleComplexOrder header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelReplaceSingleComplexOrderRequestOrder header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .auctionInitialOrder header r0 => ⟨[51, 53], ⟨[80, 73], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderSingleComplexCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassStatusRequest header r0 => ⟨[51, 53], ⟨[65, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newMultiLegOrderSingle header r0 => ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelReplaceMultiLegOrder header r0 => ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userRequest header r0 => ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [68] then
        if known (Header.tags ++ NewSingleComplexOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewSingleComplexOrder.decode rest
          pure (.newSingleComplexOrder header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ CancelReplaceSingleComplexOrderRequestOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReplaceSingleComplexOrderRequestOrder.decode rest
          pure (.cancelReplaceSingleComplexOrderRequestOrder header r0)
        else none
      else if token.value.val = [80, 73] then
        if known (Header.tags ++ AuctionInitialOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AuctionInitialOrder.decode rest
          pure (.auctionInitialOrder header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderSingleComplexCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderSingleComplexCancelRequest.decode rest
          pure (.orderSingleComplexCancelRequest header r0)
        else none
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value.val = [65, 70] then
        if known (Header.tags ++ OrderMassStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassStatusRequest.decode rest
          pure (.orderMassStatusRequest header r0)
        else none
      else if token.value.val = [65, 66] then
        if known (Header.tags ++ NewMultiLegOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewMultiLegOrderSingle.decode rest
          pure (.newMultiLegOrderSingle header r0)
        else none
      else if token.value.val = [65, 67] then
        if known (Header.tags ++ CancelReplaceMultiLegOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReplaceMultiLegOrder.decode rest
          pure (.cancelReplaceMultiLegOrder header r0)
        else none
      else if token.value.val = [66, 69] then
        if known (Header.tags ++ UserRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserRequest.decode rest
          pure (.userRequest header r0)
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

theorem Message.decode_newSingleComplexOrder (header : Header) (r0 : NewSingleComplexOrder) :
    Message.decode (Message.tokens (.newSingleComplexOrder header r0)) = some (.newSingleComplexOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewSingleComplexOrder.tags) rfl rfl (by decide +kernel))
  have c1 := NewSingleComplexOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewSingleComplexOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewSingleComplexOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_cancelReplaceSingleComplexOrderRequestOrder (header : Header) (r0 : CancelReplaceSingleComplexOrderRequestOrder) :
    Message.decode (Message.tokens (.cancelReplaceSingleComplexOrderRequestOrder header r0)) = some (.cancelReplaceSingleComplexOrderRequestOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelReplaceSingleComplexOrderRequestOrder.tags) rfl rfl (by decide +kernel))
  have c1 := CancelReplaceSingleComplexOrderRequestOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelReplaceSingleComplexOrderRequestOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelReplaceSingleComplexOrderRequestOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_auctionInitialOrder (header : Header) (r0 : AuctionInitialOrder) :
    Message.decode (Message.tokens (.auctionInitialOrder header r0)) = some (.auctionInitialOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AuctionInitialOrder.tags) rfl rfl (by decide +kernel))
  have c1 := AuctionInitialOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AuctionInitialOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AuctionInitialOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderSingleComplexCancelRequest (header : Header) (r0 : OrderSingleComplexCancelRequest) :
    Message.decode (Message.tokens (.orderSingleComplexCancelRequest header r0)) = some (.orderSingleComplexCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderSingleComplexCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderSingleComplexCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderSingleComplexCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderSingleComplexCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decode (Message.tokens (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newMultiLegOrderSingle (header : Header) (r0 : NewMultiLegOrderSingle) :
    Message.decode (Message.tokens (.newMultiLegOrderSingle header r0)) = some (.newMultiLegOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewMultiLegOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewMultiLegOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewMultiLegOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewMultiLegOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_cancelReplaceMultiLegOrder (header : Header) (r0 : CancelReplaceMultiLegOrder) :
    Message.decode (Message.tokens (.cancelReplaceMultiLegOrder header r0)) = some (.cancelReplaceMultiLegOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelReplaceMultiLegOrder.tags) rfl rfl (by decide +kernel))
  have c1 := CancelReplaceMultiLegOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelReplaceMultiLegOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelReplaceMultiLegOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userRequest (header : Header) (r0 : UserRequest) :
    Message.decode (Message.tokens (.userRequest header r0)) = some (.userRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags) rfl
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
  | newSingleComplexOrder header r0 => exact Message.decode_newSingleComplexOrder header r0
  | cancelReplaceSingleComplexOrderRequestOrder header r0 => exact Message.decode_cancelReplaceSingleComplexOrderRequestOrder header r0
  | auctionInitialOrder header r0 => exact Message.decode_auctionInitialOrder header r0
  | orderSingleComplexCancelRequest header r0 => exact Message.decode_orderSingleComplexCancelRequest header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | orderMassStatusRequest header r0 => exact Message.decode_orderMassStatusRequest header r0
  | newMultiLegOrderSingle header r0 => exact Message.decode_newMultiLegOrderSingle header r0
  | cancelReplaceMultiLegOrder header r0 => exact Message.decode_cancelReplaceMultiLegOrder header r0
  | userRequest header r0 => exact Message.decode_userRequest header r0

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

theorem Message.decodeBytes_newSingleComplexOrder (header : Header) (r0 : NewSingleComplexOrder) :
    Message.decodeBytes (Message.encode (.newSingleComplexOrder header r0)) = some (.newSingleComplexOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewSingleComplexOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newSingleComplexOrder header r0

theorem Message.decodeBytes_cancelReplaceSingleComplexOrderRequestOrder (header : Header) (r0 : CancelReplaceSingleComplexOrderRequestOrder) :
    Message.decodeBytes (Message.encode (.cancelReplaceSingleComplexOrderRequestOrder header r0)) = some (.cancelReplaceSingleComplexOrderRequestOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelReplaceSingleComplexOrderRequestOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReplaceSingleComplexOrderRequestOrder header r0

theorem Message.decodeBytes_auctionInitialOrder (header : Header) (r0 : AuctionInitialOrder) :
    Message.decodeBytes (Message.encode (.auctionInitialOrder header r0)) = some (.auctionInitialOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[80, 73], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AuctionInitialOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_auctionInitialOrder header r0

theorem Message.decodeBytes_orderSingleComplexCancelRequest (header : Header) (r0 : OrderSingleComplexCancelRequest) :
    Message.decodeBytes (Message.encode (.orderSingleComplexCancelRequest header r0)) = some (.orderSingleComplexCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderSingleComplexCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderSingleComplexCancelRequest header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decodeBytes (Message.encode (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassStatusRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassStatusRequest header r0

theorem Message.decodeBytes_newMultiLegOrderSingle (header : Header) (r0 : NewMultiLegOrderSingle) :
    Message.decodeBytes (Message.encode (.newMultiLegOrderSingle header r0)) = some (.newMultiLegOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewMultiLegOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newMultiLegOrderSingle header r0

theorem Message.decodeBytes_cancelReplaceMultiLegOrder (header : Header) (r0 : CancelReplaceMultiLegOrder) :
    Message.decodeBytes (Message.encode (.cancelReplaceMultiLegOrder header r0)) = some (.cancelReplaceMultiLegOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelReplaceMultiLegOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReplaceMultiLegOrder header r0

theorem Message.decodeBytes_userRequest (header : Header) (r0 : UserRequest) :
    Message.decodeBytes (Message.encode (.userRequest header r0)) = some (.userRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | fIXProtocolErrorReject header r0 => exact Message.decodeBytes_fIXProtocolErrorReject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newSingleComplexOrder header r0 => exact Message.decodeBytes_newSingleComplexOrder header r0
  | cancelReplaceSingleComplexOrderRequestOrder header r0 => exact Message.decodeBytes_cancelReplaceSingleComplexOrderRequestOrder header r0
  | auctionInitialOrder header r0 => exact Message.decodeBytes_auctionInitialOrder header r0
  | orderSingleComplexCancelRequest header r0 => exact Message.decodeBytes_orderSingleComplexCancelRequest header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | orderMassStatusRequest header r0 => exact Message.decodeBytes_orderMassStatusRequest header r0
  | newMultiLegOrderSingle header r0 => exact Message.decodeBytes_newMultiLegOrderSingle header r0
  | cancelReplaceMultiLegOrder header r0 => exact Message.decodeBytes_cancelReplaceMultiLegOrder header r0
  | userRequest header r0 => exact Message.decodeBytes_userRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.BoxBoxoptionsOrderentryFixV45Client
