import Wire

/-!
# Coinbase  v0.26, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CoinbaseCoinbasederivativesOrdersapiFixV026Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  origSendingTime : Option (Terminated 1)  -- tag 122
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[49, 49, 54]], [[53, 50]], [[53, 54]], [[53, 55]], [[49, 50, 50]], [[51, 54, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let lastMsgSeqNumProcessed ← readOptional [51, 54, 57] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, onBehalfOfSubID, sendingTime, targetCompID, targetSubID, origSendingTime, lastMsgSeqNumProcessed }

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
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastMsgSeqNumProcessed := readOptional_part [51, 54, 57] record.lastMsgSeqNumProcessed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, onBehalfOfSubID, sendingTime, targetCompID, targetSubID, origSendingTime, lastMsgSeqNumProcessed, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 54, 57] record.lastMsgSeqNumProcessed (by decide) (by decide))
            (paired_none pairing))))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, username, password }

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
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, username, password, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53, 52] record.password (by decide) (by decide))
       (paired_none pairing)))))

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

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
    (paired_none pairing))

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

structure Heartbeat where
  testReqID : Terminated 1  -- tag 112

def Heartbeat.parts (record : Heartbeat) : List Part :=
  [Part.required [49, 49, 50] record.testReqID]

def Heartbeat.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (tokens : List Token) : Option Heartbeat := do
  let testReqID ← readRequired [49, 49, 50] tokens
  pure { testReqID }

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (agrees : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  have distinct : Heartbeat.tags.flatten.Nodup := by decide +kernel
  have testReqID := readRequired_part [49, 49, 50] record.testReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Heartbeat.decode, testReqID, some_bind] <;> rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Terminated 1  -- tag 58
  sessionRejectReason : Terminated 1  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [53, 56] record.text,
   Part.required [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readRequired [53, 56] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
  pure { refSeqNum, text, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, sessionRejectReason, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
     (paired_none pairing)))

structure ExecutionReport where
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  timeInForce : Option (Terminated 1)  -- tag 59
  manualOrderIndicator : Terminated 1  -- tag 1028
  custOrderHandlingInst : Terminated 1  -- tag 1031

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 57] record.timeInForce,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.required [49, 48, 51, 49] record.custOrderHandlingInst]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[51, 55]], [[51, 57]], [[52, 48]], [[52, 49]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[53, 57]], [[49, 48, 50, 56]], [[49, 48, 51, 49]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let custOrderHandlingInst ← readRequired [49, 48, 51, 49] tokens
  pure { account, clOrdID, cumQty, execID, orderID, ordStatus, ordType, origClOrdID, side, symbol, securityType, timeInForce, manualOrderIndicator, custOrderHandlingInst }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have custOrderHandlingInst := readRequired_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, clOrdID, cumQty, execID, orderID, ordStatus, ordType, origClOrdID, side, symbol, securityType, timeInForce, manualOrderIndicator, custOrderHandlingInst, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 48, 51, 49] record.custOrderHandlingInst (by decide) (by decide))
                (paired_none pairing))))))))))))))

structure ExecutionReportNewOrderAck where
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  leavesQty : Terminated 1  -- tag 151
  maxShow : Option (Terminated 1)  -- tag 210
  execRestatementReason : Option (Terminated 1)  -- tag 378
  expireDate : Option (Terminated 1)  -- tag 432
  requestTime : Option (Terminated 1)  -- tag 5979
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionStrategy : Option (Terminated 1)  -- tag 8000

def ExecutionReportNewOrderAck.parts (record : ExecutionReportNewOrderAck) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 57, 55, 57] record.requestTime,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionStrategy]

def ExecutionReportNewOrderAck.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[57, 57]], [[49, 49, 48]], [[49, 53, 49]], [[50, 49, 48]], [[51, 55, 56]], [[52, 51, 50]], [[53, 57, 55, 57]], [[55, 57, 50, 56]], [[56, 48, 48, 48]]]

theorem ExecutionReportNewOrderAck.shape (record : ExecutionReportNewOrderAck) : record.parts.map Part.tags = ExecutionReportNewOrderAck.tags := rfl

def ExecutionReportNewOrderAck.decode (tokens : List Token) : Option ExecutionReportNewOrderAck := do
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionStrategy ← readOptional [56, 48, 48, 48] tokens
  pure { orderQty, price, transactTime, stopPx, minQty, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy }

theorem ExecutionReportNewOrderAck.decode_agrees (record : ExecutionReportNewOrderAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNewOrderAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNewOrderAck.decode tokens = some record := by
  have distinct : ExecutionReportNewOrderAck.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have selfMatchPreventionStrategy := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [ExecutionReportNewOrderAck.decode, orderQty, price, transactTime, stopPx, minQty, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy, some_bind] <;> rfl

theorem ExecutionReportNewOrderAck.taken (record : ExecutionReportNewOrderAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionStrategy (by decide) (by decide))
              (paired_none pairing))))))))))))

structure ExecutionReportModifyAck where
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  leavesQty : Terminated 1  -- tag 151
  maxShow : Option (Terminated 1)  -- tag 210
  execRestatementReason : Option (Terminated 1)  -- tag 378
  expireDate : Option (Terminated 1)  -- tag 432
  requestTime : Option (Terminated 1)  -- tag 5979
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionStrategy : Option (Terminated 1)  -- tag 8000

def ExecutionReportModifyAck.parts (record : ExecutionReportModifyAck) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 57, 55, 57] record.requestTime,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionStrategy]

def ExecutionReportModifyAck.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[57, 57]], [[49, 49, 48]], [[49, 53, 49]], [[50, 49, 48]], [[51, 55, 56]], [[52, 51, 50]], [[53, 57, 55, 57]], [[55, 57, 50, 56]], [[56, 48, 48, 48]]]

theorem ExecutionReportModifyAck.shape (record : ExecutionReportModifyAck) : record.parts.map Part.tags = ExecutionReportModifyAck.tags := rfl

def ExecutionReportModifyAck.decode (tokens : List Token) : Option ExecutionReportModifyAck := do
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionStrategy ← readOptional [56, 48, 48, 48] tokens
  pure { orderQty, price, transactTime, stopPx, minQty, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy }

theorem ExecutionReportModifyAck.decode_agrees (record : ExecutionReportModifyAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportModifyAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportModifyAck.decode tokens = some record := by
  have distinct : ExecutionReportModifyAck.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have selfMatchPreventionStrategy := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [ExecutionReportModifyAck.decode, orderQty, price, transactTime, stopPx, minQty, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy, some_bind] <;> rfl

theorem ExecutionReportModifyAck.taken (record : ExecutionReportModifyAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionStrategy (by decide) (by decide))
              (paired_none pairing))))))))))))

structure ExecutionReportCancelAck where
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  stopPx : Option (Terminated 1)  -- tag 99
  leavesQty : Terminated 1  -- tag 151
  maxShow : Option (Terminated 1)  -- tag 210
  execRestatementReason : Option (Terminated 1)  -- tag 378
  expireDate : Option (Terminated 1)  -- tag 432
  requestTime : Option (Terminated 1)  -- tag 5979
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionStrategy : Option (Terminated 1)  -- tag 8000

def ExecutionReportCancelAck.parts (record : ExecutionReportCancelAck) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [57, 57] record.stopPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 57, 55, 57] record.requestTime,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionStrategy]

def ExecutionReportCancelAck.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[57, 57]], [[49, 53, 49]], [[50, 49, 48]], [[51, 55, 56]], [[52, 51, 50]], [[53, 57, 55, 57]], [[55, 57, 50, 56]], [[56, 48, 48, 48]]]

theorem ExecutionReportCancelAck.shape (record : ExecutionReportCancelAck) : record.parts.map Part.tags = ExecutionReportCancelAck.tags := rfl

def ExecutionReportCancelAck.decode (tokens : List Token) : Option ExecutionReportCancelAck := do
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let stopPx ← readOptional [57, 57] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionStrategy ← readOptional [56, 48, 48, 48] tokens
  pure { orderQty, price, transactTime, stopPx, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy }

theorem ExecutionReportCancelAck.decode_agrees (record : ExecutionReportCancelAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelAck.decode tokens = some record := by
  have distinct : ExecutionReportCancelAck.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchPreventionStrategy := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportCancelAck.decode, orderQty, price, transactTime, stopPx, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy, some_bind] <;> rfl

theorem ExecutionReportCancelAck.taken (record : ExecutionReportCancelAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionStrategy (by decide) (by decide))
             (paired_none pairing)))))))))))

structure ExecutionReportStopTrigger where
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  stopPx : Option (Terminated 1)  -- tag 99
  leavesQty : Terminated 1  -- tag 151
  maxShow : Option (Terminated 1)  -- tag 210
  execRestatementReason : Option (Terminated 1)  -- tag 378
  expireDate : Option (Terminated 1)  -- tag 432
  requestTime : Option (Terminated 1)  -- tag 5979
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionStrategy : Option (Terminated 1)  -- tag 8000

def ExecutionReportStopTrigger.parts (record : ExecutionReportStopTrigger) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [57, 57] record.stopPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 57, 55, 57] record.requestTime,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionStrategy]

def ExecutionReportStopTrigger.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[57, 57]], [[49, 53, 49]], [[50, 49, 48]], [[51, 55, 56]], [[52, 51, 50]], [[53, 57, 55, 57]], [[55, 57, 50, 56]], [[56, 48, 48, 48]]]

theorem ExecutionReportStopTrigger.shape (record : ExecutionReportStopTrigger) : record.parts.map Part.tags = ExecutionReportStopTrigger.tags := rfl

def ExecutionReportStopTrigger.decode (tokens : List Token) : Option ExecutionReportStopTrigger := do
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let stopPx ← readOptional [57, 57] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionStrategy ← readOptional [56, 48, 48, 48] tokens
  pure { orderQty, price, transactTime, stopPx, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy }

theorem ExecutionReportStopTrigger.decode_agrees (record : ExecutionReportStopTrigger) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportStopTrigger.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportStopTrigger.decode tokens = some record := by
  have distinct : ExecutionReportStopTrigger.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have selfMatchPreventionStrategy := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportStopTrigger.decode, orderQty, price, transactTime, stopPx, leavesQty, maxShow, execRestatementReason, expireDate, requestTime, selfMatchPreventionID, selfMatchPreventionStrategy, some_bind] <;> rfl

theorem ExecutionReportStopTrigger.taken (record : ExecutionReportStopTrigger) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionStrategy (by decide) (by decide))
             (paired_none pairing)))))))))))

structure ExecutionReportTrade where
  trdMatchID : Terminated 1  -- tag 880
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  avgPx : Option (Terminated 1)  -- tag 6
  transactTime : Terminated 1  -- tag 60
  tradeDate : Terminated 1  -- tag 75
  leavesQty : Option (Terminated 1)  -- tag 151
  totalNumSecurities : Option (Terminated 1)  -- tag 393
  multiLegReportingType : Option (Terminated 1)  -- tag 442
  secondaryExecID : Option (Terminated 1)  -- tag 527
  aggressorIndicator : Option (Terminated 1)  -- tag 1057
  requestTime : Option (Terminated 1)  -- tag 5979

def ExecutionReportTrade.parts (record : ExecutionReportTrade) : List Part :=
  [Part.required [56, 56, 48] record.trdMatchID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [54] record.avgPx,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 53] record.tradeDate,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [51, 57, 51] record.totalNumSecurities,
   Part.optional [52, 52, 50] record.multiLegReportingType,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [49, 48, 53, 55] record.aggressorIndicator,
   Part.optional [53, 57, 55, 57] record.requestTime]

def ExecutionReportTrade.tags : List (List (List UInt8)) :=
  [[[56, 56, 48]], [[51, 49]], [[51, 50]], [[51, 56]], [[52, 52]], [[54]], [[54, 48]], [[55, 53]], [[49, 53, 49]], [[51, 57, 51]], [[52, 52, 50]], [[53, 50, 55]], [[49, 48, 53, 55]], [[53, 57, 55, 57]]]

theorem ExecutionReportTrade.shape (record : ExecutionReportTrade) : record.parts.map Part.tags = ExecutionReportTrade.tags := rfl

def ExecutionReportTrade.decode (tokens : List Token) : Option ExecutionReportTrade := do
  let trdMatchID ← readRequired [56, 56, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let avgPx ← readOptional [54] tokens
  let transactTime ← readRequired [54, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let totalNumSecurities ← readOptional [51, 57, 51] tokens
  let multiLegReportingType ← readOptional [52, 52, 50] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let aggressorIndicator ← readOptional [49, 48, 53, 55] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  pure { trdMatchID, lastPx, lastQty, orderQty, price, avgPx, transactTime, tradeDate, leavesQty, totalNumSecurities, multiLegReportingType, secondaryExecID, aggressorIndicator, requestTime }

theorem ExecutionReportTrade.decode_agrees (record : ExecutionReportTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTrade.decode tokens = some record := by
  have distinct : ExecutionReportTrade.tags.flatten.Nodup := by decide +kernel
  have trdMatchID := readRequired_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have totalNumSecurities := readOptional_part [51, 57, 51] record.totalNumSecurities tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have multiLegReportingType := readOptional_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have aggressorIndicator := readOptional_part [49, 48, 53, 55] record.aggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [ExecutionReportTrade.decode, trdMatchID, lastPx, lastQty, orderQty, price, avgPx, transactTime, tradeDate, leavesQty, totalNumSecurities, multiLegReportingType, secondaryExecID, aggressorIndicator, requestTime, some_bind] <;> rfl

theorem ExecutionReportTrade.taken (record : ExecutionReportTrade) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54] record.avgPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 57, 51] record.totalNumSecurities (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 52, 50] record.multiLegReportingType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 50, 55] record.secondaryExecID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 48, 53, 55] record.aggressorIndicator (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
                (paired_none pairing))))))))))))))

structure ExecutionReportRejectAck where
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  tradeDate : Terminated 1  -- tag 75
  ordRejReason : Option (Terminated 1)  -- tag 103
  leavesQty : Option (Terminated 1)  -- tag 151

def ExecutionReportRejectAck.parts (record : ExecutionReportRejectAck) : List Part :=
  [Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 53] record.tradeDate,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 53, 49] record.leavesQty]

def ExecutionReportRejectAck.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[53, 56]], [[54, 48]], [[55, 53]], [[49, 48, 51]], [[49, 53, 49]]]

theorem ExecutionReportRejectAck.shape (record : ExecutionReportRejectAck) : record.parts.map Part.tags = ExecutionReportRejectAck.tags := rfl

def ExecutionReportRejectAck.decode (tokens : List Token) : Option ExecutionReportRejectAck := do
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  pure { orderQty, price, text, transactTime, tradeDate, ordRejReason, leavesQty }

theorem ExecutionReportRejectAck.decode_agrees (record : ExecutionReportRejectAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejectAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejectAck.decode tokens = some record := by
  have distinct : ExecutionReportRejectAck.tags.flatten.Nodup := by decide +kernel
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [ExecutionReportRejectAck.decode, orderQty, price, text, transactTime, tradeDate, ordRejReason, leavesQty, some_bind] <;> rfl

theorem ExecutionReportRejectAck.taken (record : ExecutionReportRejectAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
         (paired_none pairing)))))))

structure ExecutionReportDoneForDay where
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60
  tradeDate : Terminated 1  -- tag 75
  leavesQty : Option (Terminated 1)  -- tag 151
  requestTime : Option (Terminated 1)  -- tag 5979

def ExecutionReportDoneForDay.parts (record : ExecutionReportDoneForDay) : List Part :=
  [Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 53] record.tradeDate,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [53, 57, 55, 57] record.requestTime]

def ExecutionReportDoneForDay.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[55, 53]], [[49, 53, 49]], [[53, 57, 55, 57]]]

theorem ExecutionReportDoneForDay.shape (record : ExecutionReportDoneForDay) : record.parts.map Part.tags = ExecutionReportDoneForDay.tags := rfl

def ExecutionReportDoneForDay.decode (tokens : List Token) : Option ExecutionReportDoneForDay := do
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  pure { orderQty, price, transactTime, tradeDate, leavesQty, requestTime }

theorem ExecutionReportDoneForDay.decode_agrees (record : ExecutionReportDoneForDay) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportDoneForDay.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportDoneForDay.decode tokens = some record := by
  have distinct : ExecutionReportDoneForDay.tags.flatten.Nodup := by decide +kernel
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportDoneForDay.decode, orderQty, price, transactTime, tradeDate, leavesQty, requestTime, some_bind] <;> rfl

theorem ExecutionReportDoneForDay.taken (record : ExecutionReportDoneForDay) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
        (paired_none pairing))))))

structure ExecutionReportEliminationAck where
  orderQty : Terminated 1  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  transactTime : Option (Terminated 1)  -- tag 60
  minQty : Option (Terminated 1)  -- tag 110
  leavesQty : Terminated 1  -- tag 151
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionStrategy : Option (Terminated 1)  -- tag 8000
  requestTime : Option (Terminated 1)  -- tag 5979

def ExecutionReportEliminationAck.parts (record : ExecutionReportEliminationAck) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionStrategy,
   Part.optional [53, 57, 55, 57] record.requestTime]

def ExecutionReportEliminationAck.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 52]], [[54, 48]], [[49, 49, 48]], [[49, 53, 49]], [[55, 57, 50, 56]], [[56, 48, 48, 48]], [[53, 57, 55, 57]]]

theorem ExecutionReportEliminationAck.shape (record : ExecutionReportEliminationAck) : record.parts.map Part.tags = ExecutionReportEliminationAck.tags := rfl

def ExecutionReportEliminationAck.decode (tokens : List Token) : Option ExecutionReportEliminationAck := do
  let orderQty ← readRequired [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionStrategy ← readOptional [56, 48, 48, 48] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  pure { orderQty, price, transactTime, minQty, leavesQty, selfMatchPreventionID, selfMatchPreventionStrategy, requestTime }

theorem ExecutionReportEliminationAck.decode_agrees (record : ExecutionReportEliminationAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportEliminationAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportEliminationAck.decode tokens = some record := by
  have distinct : ExecutionReportEliminationAck.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have selfMatchPreventionStrategy := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [ExecutionReportEliminationAck.decode, orderQty, price, transactTime, minQty, leavesQty, selfMatchPreventionID, selfMatchPreventionStrategy, requestTime, some_bind] <;> rfl

theorem ExecutionReportEliminationAck.taken (record : ExecutionReportEliminationAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionStrategy (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
          (paired_none pairing))))))))

structure OrderCancelReject where
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Option (Terminated 1)  -- tag 41
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  cxlRejReason : Option (Terminated 1)  -- tag 102
  cxlRejResponseTo : Terminated 1  -- tag 434
  requestTime : Option (Terminated 1)  -- tag 5979

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [53, 57, 55, 57] record.requestTime]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 53]], [[53, 56]], [[54, 48]], [[49, 48, 50]], [[52, 51, 52]], [[53, 57, 55, 57]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  pure { account, clOrdID, orderID, ordStatus, origClOrdID, symbol, text, transactTime, cxlRejReason, cxlRejResponseTo, requestTime }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [OrderCancelReject.decode, account, clOrdID, orderID, ordStatus, origClOrdID, symbol, text, transactTime, cxlRejReason, cxlRejResponseTo, requestTime, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
             (paired_none pairing)))))))))))

structure LastExecId where
  refSeqNum : Terminated 1  -- tag 45
  execID : Terminated 1  -- tag 17

def LastExecId.parts (record : LastExecId) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [49, 55] record.execID]

def LastExecId.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[49, 55]]]

theorem LastExecId.shape (record : LastExecId) : record.parts.map Part.tags = LastExecId.tags := rfl

def LastExecId.decode (tokens : List Token) : Option LastExecId := do
  let refSeqNum ← readRequired [52, 53] tokens
  let execID ← readRequired [49, 55] tokens
  pure { refSeqNum, execID }

theorem LastExecId.decode_agrees (record : LastExecId) (tokens : List Token)
    (agrees : ∀ tags ∈ LastExecId.tags, select tags tokens = select tags (encodeParts record.parts)) :
    LastExecId.decode tokens = some record := by
  have distinct : LastExecId.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [LastExecId.decode, refSeqNum, execID, some_bind] <;> rfl

theorem LastExecId.taken (record : LastExecId) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
    (paired_none pairing))

structure EventResendComplete where
  refSeqNum : Terminated 1  -- tag 45
  resentEventCount : Terminated 1  -- tag 22005

def EventResendComplete.parts (record : EventResendComplete) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [50, 50, 48, 48, 53] record.resentEventCount]

def EventResendComplete.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[50, 50, 48, 48, 53]]]

theorem EventResendComplete.shape (record : EventResendComplete) : record.parts.map Part.tags = EventResendComplete.tags := rfl

def EventResendComplete.decode (tokens : List Token) : Option EventResendComplete := do
  let refSeqNum ← readRequired [52, 53] tokens
  let resentEventCount ← readRequired [50, 50, 48, 48, 53] tokens
  pure { refSeqNum, resentEventCount }

theorem EventResendComplete.decode_agrees (record : EventResendComplete) (tokens : List Token)
    (agrees : ∀ tags ∈ EventResendComplete.tags, select tags tokens = select tags (encodeParts record.parts)) :
    EventResendComplete.decode tokens = some record := by
  have distinct : EventResendComplete.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have resentEventCount := readRequired_part [50, 50, 48, 48, 53] record.resentEventCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [EventResendComplete.decode, refSeqNum, resentEventCount, some_bind] <;> rfl

theorem EventResendComplete.taken (record : EventResendComplete) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 50, 48, 48, 53] record.resentEventCount (by decide) (by decide))
    (paired_none pairing))

structure EventResendReject where
  refSeqNum : Terminated 1  -- tag 45
  eventResendRejectReason : Terminated 1  -- tag 22006
  text : Option (Terminated 1)  -- tag 58

def EventResendReject.parts (record : EventResendReject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [50, 50, 48, 48, 54] record.eventResendRejectReason,
   Part.optional [53, 56] record.text]

def EventResendReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[50, 50, 48, 48, 54]], [[53, 56]]]

theorem EventResendReject.shape (record : EventResendReject) : record.parts.map Part.tags = EventResendReject.tags := rfl

def EventResendReject.decode (tokens : List Token) : Option EventResendReject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let eventResendRejectReason ← readRequired [50, 50, 48, 48, 54] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, eventResendRejectReason, text }

theorem EventResendReject.decode_agrees (record : EventResendReject) (tokens : List Token)
    (agrees : ∀ tags ∈ EventResendReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    EventResendReject.decode tokens = some record := by
  have distinct : EventResendReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventResendRejectReason := readRequired_part [50, 50, 48, 48, 54] record.eventResendRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [EventResendReject.decode, refSeqNum, eventResendRejectReason, text, some_bind] <;> rfl

theorem EventResendReject.taken (record : EventResendReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 50, 48, 48, 54] record.eventResendRejectReason (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_none pairing)))

structure BusinessMessageReject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Terminated 1  -- tag 380

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [51, 56, 48] record.businessRejectReason]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 57]], [[51, 56, 48]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  pure { refSeqNum, text, businessRejectRefID, businessRejectReason }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, text, businessRejectRefID, businessRejectReason, some_bind] <;> rfl

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 57] record.businessRejectRefID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
      (paired_none pairing))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | reject (header : Header) (r0 : Reject)
  | executionReportNewOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewOrderAck)
  | executionReportModifyAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportModifyAck)
  | executionReportCancelAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelAck)
  | executionReportStopTrigger (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportStopTrigger)
  | executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade)
  | executionReportRejectAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectAck)
  | executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay)
  | executionReportEliminationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportEliminationAck)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | lastExecId (header : Header) (r0 : LastExecId)
  | eventResendComplete (header : Header) (r0 : EventResendComplete)
  | eventResendReject (header : Header) (r0 : EventResendReject)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNewOrderAck header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportModifyAck header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportCancelAck header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportStopTrigger header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts)
  | .executionReportTrade header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .executionReportRejectAck header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportDoneForDay header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts)
  | .executionReportEliminationAck header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .lastExecId header r0 => ⟨[51, 53], [70, 50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eventResendComplete header r0 => ⟨[51, 53], [70, 52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eventResendReject header r0 => ⟨[51, 53], [70, 53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else if token.value = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
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
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewOrderAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNewOrderAck.decode rest
              pure (.executionReportNewOrderAck header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportModifyAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportModifyAck.decode rest
              pure (.executionReportModifyAck header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelAck.decode rest
              pure (.executionReportCancelAck header r0 r1)
            else none
          else if key.val = [76] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportStopTrigger.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportStopTrigger.decode rest
              pure (.executionReportStopTrigger header r0 r1)
            else none
          else if key.val = [70] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTrade.decode rest
              pure (.executionReportTrade header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejectAck.decode rest
              pure (.executionReportRejectAck header r0 r1)
            else none
          else if key.val = [51] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportDoneForDay.decode rest
              pure (.executionReportDoneForDay header r0 r1)
            else none
          else if key.val = [67] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportEliminationAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportEliminationAck.decode rest
              pure (.executionReportEliminationAck header r0 r1)
            else none
          else none
      else if token.value = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value = [70, 50] then
        if known (Header.tags ++ LastExecId.tags) rest then do
          let header ← Header.decode rest
          let r0 ← LastExecId.decode rest
          pure (.lastExecId header r0)
        else none
      else if token.value = [70, 52] then
        if known (Header.tags ++ EventResendComplete.tags) rest then do
          let header ← Header.decode rest
          let r0 ← EventResendComplete.decode rest
          pure (.eventResendComplete header r0)
        else none
      else if token.value = [70, 53] then
        if known (Header.tags ++ EventResendReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← EventResendReject.decode rest
          pure (.eventResendReject header r0)
        else none
      else if token.value = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
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

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportNewOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewOrderAck) :
    Message.decode (Message.tokens (.executionReportNewOrderAck header r0 r1)) = some (.executionReportNewOrderAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewOrderAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNewOrderAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNewOrderAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNewOrderAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNewOrderAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewOrderAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportModifyAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportModifyAck) :
    Message.decode (Message.tokens (.executionReportModifyAck header r0 r1)) = some (.executionReportModifyAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportModifyAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportModifyAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportModifyAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportModifyAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportModifyAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportModifyAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelAck) :
    Message.decode (Message.tokens (.executionReportCancelAck header r0 r1)) = some (.executionReportCancelAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportStopTrigger (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportStopTrigger) :
    Message.decode (Message.tokens (.executionReportStopTrigger header r0 r1)) = some (.executionReportStopTrigger header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportStopTrigger.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportStopTrigger.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[76], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[76], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportStopTrigger.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportStopTrigger.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportStopTrigger.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportStopTrigger.tags) rfl
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

theorem Message.decode_executionReportRejectAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectAck) :
    Message.decode (Message.tokens (.executionReportRejectAck header r0 r1)) = some (.executionReportRejectAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejectAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejectAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejectAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejectAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay) :
    Message.decode (Message.tokens (.executionReportDoneForDay header r0 r1)) = some (.executionReportDoneForDay header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[51], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportDoneForDay.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportDoneForDay.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportEliminationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportEliminationAck) :
    Message.decode (Message.tokens (.executionReportEliminationAck header r0 r1)) = some (.executionReportEliminationAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportEliminationAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportEliminationAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportEliminationAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportEliminationAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportEliminationAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportEliminationAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_lastExecId (header : Header) (r0 : LastExecId) :
    Message.decode (Message.tokens (.lastExecId header r0)) = some (.lastExecId header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (LastExecId.tags) rfl rfl (by decide +kernel))
  have c1 := LastExecId.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (LastExecId.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ LastExecId.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_eventResendComplete (header : Header) (r0 : EventResendComplete) :
    Message.decode (Message.tokens (.eventResendComplete header r0)) = some (.eventResendComplete header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (EventResendComplete.tags) rfl rfl (by decide +kernel))
  have c1 := EventResendComplete.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (EventResendComplete.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ EventResendComplete.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_eventResendReject (header : Header) (r0 : EventResendReject) :
    Message.decode (Message.tokens (.eventResendReject header r0)) = some (.eventResendReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (EventResendReject.tags) rfl rfl (by decide +kernel))
  have c1 := EventResendReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (EventResendReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ EventResendReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | reject header r0 => exact Message.decode_reject header r0
  | executionReportNewOrderAck header r0 r1 => exact Message.decode_executionReportNewOrderAck header r0 r1
  | executionReportModifyAck header r0 r1 => exact Message.decode_executionReportModifyAck header r0 r1
  | executionReportCancelAck header r0 r1 => exact Message.decode_executionReportCancelAck header r0 r1
  | executionReportStopTrigger header r0 r1 => exact Message.decode_executionReportStopTrigger header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decode_executionReportTrade header r0 r1
  | executionReportRejectAck header r0 r1 => exact Message.decode_executionReportRejectAck header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decode_executionReportDoneForDay header r0 r1
  | executionReportEliminationAck header r0 r1 => exact Message.decode_executionReportEliminationAck header r0 r1
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | lastExecId header r0 => exact Message.decode_lastExecId header r0
  | eventResendComplete header r0 => exact Message.decode_eventResendComplete header r0
  | eventResendReject header r0 => exact Message.decode_eventResendReject header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logout.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [49]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TestRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_executionReportNewOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewOrderAck) :
    Message.decodeBytes (Message.encode (.executionReportNewOrderAck header r0 r1)) = some (.executionReportNewOrderAck header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportNewOrderAck.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNewOrderAck header r0 r1

theorem Message.decodeBytes_executionReportModifyAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportModifyAck) :
    Message.decodeBytes (Message.encode (.executionReportModifyAck header r0 r1)) = some (.executionReportModifyAck header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[53], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[53], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportModifyAck.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportModifyAck header r0 r1

theorem Message.decodeBytes_executionReportCancelAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelAck) :
    Message.decodeBytes (Message.encode (.executionReportCancelAck header r0 r1)) = some (.executionReportCancelAck header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[52], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[52], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportCancelAck.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelAck header r0 r1

theorem Message.decodeBytes_executionReportStopTrigger (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportStopTrigger) :
    Message.decodeBytes (Message.encode (.executionReportStopTrigger header r0 r1)) = some (.executionReportStopTrigger header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[76], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[76], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[76], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportStopTrigger.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportStopTrigger header r0 r1

theorem Message.decodeBytes_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decodeBytes (Message.encode (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[70], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[70], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTrade.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTrade header r0 r1

theorem Message.decodeBytes_executionReportRejectAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectAck) :
    Message.decodeBytes (Message.encode (.executionReportRejectAck header r0 r1)) = some (.executionReportRejectAck header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[56], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[56], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRejectAck.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejectAck header r0 r1

theorem Message.decodeBytes_executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay) :
    Message.decodeBytes (Message.encode (.executionReportDoneForDay header r0 r1)) = some (.executionReportDoneForDay header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[51], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[51], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportDoneForDay.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportDoneForDay header r0 r1

theorem Message.decodeBytes_executionReportEliminationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportEliminationAck) :
    Message.decodeBytes (Message.encode (.executionReportEliminationAck header r0 r1)) = some (.executionReportEliminationAck header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[67], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[67], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportEliminationAck.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportEliminationAck header r0 r1

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_lastExecId (header : Header) (r0 : LastExecId) :
    Message.decodeBytes (Message.encode (.lastExecId header r0)) = some (.lastExecId header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 50]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (LastExecId.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_lastExecId header r0

theorem Message.decodeBytes_eventResendComplete (header : Header) (r0 : EventResendComplete) :
    Message.decodeBytes (Message.encode (.eventResendComplete header r0)) = some (.eventResendComplete header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (EventResendComplete.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eventResendComplete header r0

theorem Message.decodeBytes_eventResendReject (header : Header) (r0 : EventResendReject) :
    Message.decodeBytes (Message.encode (.eventResendReject header r0)) = some (.eventResendReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (EventResendReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eventResendReject header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [106]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | executionReportNewOrderAck header r0 r1 => exact Message.decodeBytes_executionReportNewOrderAck header r0 r1
  | executionReportModifyAck header r0 r1 => exact Message.decodeBytes_executionReportModifyAck header r0 r1
  | executionReportCancelAck header r0 r1 => exact Message.decodeBytes_executionReportCancelAck header r0 r1
  | executionReportStopTrigger header r0 r1 => exact Message.decodeBytes_executionReportStopTrigger header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decodeBytes_executionReportTrade header r0 r1
  | executionReportRejectAck header r0 r1 => exact Message.decodeBytes_executionReportRejectAck header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decodeBytes_executionReportDoneForDay header r0 r1
  | executionReportEliminationAck header r0 r1 => exact Message.decodeBytes_executionReportEliminationAck header r0 r1
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | lastExecId header r0 => exact Message.decodeBytes_lastExecId header r0
  | eventResendComplete header r0 => exact Message.decodeBytes_eventResendComplete header r0
  | eventResendReject header r0 => exact Message.decodeBytes_eventResendReject header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseCoinbasederivativesOrdersapiFixV026Exchange
