import Wire

/-!
# Miami International Holdings Order Entry v2.1.d, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.MiaxMiaxoptionsOrderentryFixV21DClient

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID }

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
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 50, 57] record.deliverToSubID (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure Logon where
  rawDataLength : Option (Terminated 1)  -- tag 95
  rawData : Option (Terminated 1)  -- tag 96
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141

def Logon.parts (record : Logon) : List Part :=
  [Part.optional [57, 53] record.rawDataLength,
   Part.optional [57, 54] record.rawData,
   Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 53]], [[57, 54]], [[57, 56]], [[49, 48, 56]], [[49, 52, 49]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let rawDataLength ← readOptional [57, 53] tokens
  let rawData ← readOptional [57, 54] tokens
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  pure { rawDataLength, rawData, encryptMethod, heartBtInt, resetSeqNumFlag }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have rawDataLength := readOptional_part [57, 53] record.rawDataLength tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rawData := readOptional_part [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, rawDataLength, rawData, encryptMethod, heartBtInt, resetSeqNumFlag, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [57, 53] record.rawDataLength (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 54] record.rawData (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
       (paired_none pairing)))))

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Terminated 1  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
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
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_none pairing)))))

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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Option (Terminated 1)  -- tag 77
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  coveredOrUncovered : Option (Terminated 1)  -- tag 203
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  clientID : Option (Terminated 1)  -- tag 109
  allocAccount : Option (Terminated 1)  -- tag 79
  text : Option (Terminated 1)  -- tag 58
  maxPriceLevels : Option (Terminated 1)  -- tag 1090
  auctionID : Option (Terminated 1)  -- tag 9385
  billingMPID : Option (Terminated 1)  -- tag 9449
  attributableOrderIndicator : Option (Terminated 1)  -- tag 9732

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [55, 55] record.openClose,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 51] record.coveredOrUncovered,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 57, 48] record.maxPriceLevels,
   Part.optional [57, 51, 56, 53] record.auctionID,
   Part.optional [57, 52, 52, 57] record.billingMPID,
   Part.optional [57, 55, 51, 50] record.attributableOrderIndicator]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 51]], [[50, 48, 52]], [[50, 48, 53]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 57]], [[55, 57]], [[53, 56]], [[49, 48, 57, 48]], [[57, 51, 56, 53]], [[57, 52, 52, 57]], [[57, 55, 51, 50]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readOptional [55, 55] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let coveredOrUncovered ← readOptional [50, 48, 51] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let text ← readOptional [53, 56] tokens
  let maxPriceLevels ← readOptional [49, 48, 57, 48] tokens
  let auctionID ← readOptional [57, 51, 56, 53] tokens
  let billingMPID ← readOptional [57, 52, 52, 57] tokens
  let attributableOrderIndicator ← readOptional [57, 55, 51, 50] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, transactTime, execBroker, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, coveredOrUncovered, customerOrFirm, maturityDay, clearingFirm, clearingAccount, clientID, allocAccount, text, maxPriceLevels, auctionID, billingMPID, attributableOrderIndicator }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have coveredOrUncovered := readOptional_part [50, 48, 51] record.coveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maxPriceLevels := readOptional_part [49, 48, 57, 48] record.maxPriceLevels tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 56, 53] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have billingMPID := readOptional_part [57, 52, 52, 57] record.billingMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have attributableOrderIndicator := readOptional_part [57, 55, 51, 50] record.attributableOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, transactTime, execBroker, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, coveredOrUncovered, customerOrFirm, maturityDay, clearingFirm, clearingAccount, clientID, allocAccount, text, maxPriceLevels, auctionID, billingMPID, attributableOrderIndicator, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.openClose (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 51] record.coveredOrUncovered (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57, 48] record.maxPriceLevels (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 51, 56, 53] record.auctionID (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billingMPID (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 55, 51, 50] record.attributableOrderIndicator (by decide) (by decide))
                              (paired_none pairing))))))))))))))))))))))))))))

structure NoAllocs where
  allocQty : Terminated 1  -- tag 80
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  openClose : Option (Terminated 1)  -- tag 77
  customerOrFirm : Terminated 1  -- tag 204
  coveredOrUncovered : Option (Terminated 1)  -- tag 203
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  individualAllocID : Option (Terminated 1)  -- tag 467
  firmMPID : Terminated 1  -- tag 9946
  billingMPID : Option (Terminated 1)  -- tag 9449

def NoAllocs.parts (record : NoAllocs) : List Part :=
  [Part.required [56, 48] record.allocQty,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.optional [55, 55] record.openClose,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 51] record.coveredOrUncovered,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [52, 54, 55] record.individualAllocID,
   Part.required [57, 57, 52, 54] record.firmMPID,
   Part.optional [57, 52, 52, 57] record.billingMPID]

def NoAllocs.tags : List (List (List UInt8)) :=
  [[[56, 48]], [[49]], [[53, 56]], [[55, 55]], [[50, 48, 52]], [[50, 48, 51]], [[52, 51, 57]], [[52, 52, 48]], [[52, 54, 55]], [[57, 57, 52, 54]], [[57, 52, 52, 57]]]

theorem NoAllocs.shape (record : NoAllocs) : record.parts.map Part.tags = NoAllocs.tags := rfl

def NoAllocs.decode (tokens : List Token) : Option NoAllocs := do
  let allocQty ← readRequired [56, 48] tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let openClose ← readOptional [55, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let coveredOrUncovered ← readOptional [50, 48, 51] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let individualAllocID ← readOptional [52, 54, 55] tokens
  let firmMPID ← readRequired [57, 57, 52, 54] tokens
  let billingMPID ← readOptional [57, 52, 52, 57] tokens
  pure { allocQty, account, text, openClose, customerOrFirm, coveredOrUncovered, clearingFirm, clearingAccount, individualAllocID, firmMPID, billingMPID }

theorem NoAllocs.decode_agrees (record : NoAllocs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocs.decode tokens = some record := by
  have distinct : NoAllocs.tags.flatten.Nodup := by decide +kernel
  have allocQty := readRequired_part [56, 48] record.allocQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have coveredOrUncovered := readOptional_part [50, 48, 51] record.coveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have individualAllocID := readOptional_part [52, 54, 55] record.individualAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have firmMPID := readRequired_part [57, 57, 52, 54] record.firmMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have billingMPID := readOptional_part [57, 52, 52, 57] record.billingMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [NoAllocs.decode, allocQty, account, text, openClose, customerOrFirm, coveredOrUncovered, clearingFirm, clearingAccount, individualAllocID, firmMPID, billingMPID, some_bind] <;> rfl

theorem NoAllocs.taken (record : NoAllocs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [56, 48] record.allocQty (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.openClose (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 51] record.coveredOrUncovered (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 54, 55] record.individualAllocID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [57, 57, 52, 54] record.firmMPID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billingMPID (by decide) (by decide))
             (paired_none pairing)))))))))))

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

structure NoSide where
  side : Terminated 1  -- tag 54
  clOrdID : Terminated 1  -- tag 11
  noAllocs : List NoAllocs  -- tag 78
  allocAccount : Option (Terminated 1)  -- tag 79
  attributableOrderIndicator : Option (Terminated 1)  -- tag 9732

def NoSide.parts (record : NoSide) : List Part :=
  [Part.required [53, 52] record.side,
   Part.required [49, 49] record.clOrdID,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [57, 55, 51, 50] record.attributableOrderIndicator]

def NoSide.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 49]], [55, 56] :: NoAllocs.members, [[55, 57]], [[57, 55, 51, 50]]]

theorem NoSide.shape (record : NoSide) : record.parts.map Part.tags = NoSide.tags := rfl

def NoSide.decode (tokens : List Token) : Option NoSide := do
  let side ← readRequired [53, 52] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let noAllocs ← readGroup [55, 56] [56, 48] NoAllocs.members NoAllocs.decode tokens
  let allocAccount ← readOptional [55, 57] tokens
  let attributableOrderIndicator ← readOptional [57, 55, 51, 50] tokens
  pure { side, clOrdID, noAllocs, allocAccount, attributableOrderIndicator }

theorem NoSide.decode_agrees (record : NoSide) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSide.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSide.decode tokens = some record := by
  have distinct : NoSide.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [56, 48] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have attributableOrderIndicator := readOptional_part [57, 55, 51, 50] record.attributableOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoSide.decode, side, clOrdID, noAllocs, allocAccount, attributableOrderIndicator, some_bind] <;> rfl

theorem NoSide.taken (record : NoSide) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within (by decide) (by decide) NoAllocs.taken record.noAllocs)
     (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 55, 51, 50] record.attributableOrderIndicator (by decide) (by decide))
       (paired_none pairing)))))

def NoSide.members : List (List UInt8) := NoSide.tags.flatten

def NoSide.encode (entry : NoSide) : List Token := encodeParts entry.parts

theorem NoSide.decode_encode (entry : NoSide) : NoSide.decode entry.encode = some entry :=
  NoSide.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSide.within (entry : NoSide) : ∀ token ∈ entry.encode, token.tag ∈ NoSide.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSide.shape] at this

theorem NoSide.led (entry : NoSide) : Lead [53, 52] entry.encode :=
  lead_parts [53, 52] entry.side _ NoSide.tags.tail rfl (by decide +kernel)

structure NewOrderCross where
  crossID : Terminated 1  -- tag 548
  crossType : Terminated 1  -- tag 549
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  noSide : List NoSide  -- tag 552
  autoMatchOrdType : Option (Terminated 1)  -- tag 9040
  autoMatchPrice : Option (Terminated 1)  -- tag 9044
  underlyingPrice : Option (Terminated 1)  -- tag 810
  underlyingQty : Option (Terminated 1)  -- tag 879
  priceDelta : Option (Terminated 1)  -- tag 9811
  underlyingExecutionTime : Option (Terminated 1)  -- tag 9812
  underlyingExecutionExchange : Option (Terminated 1)  -- tag 9813

def NewOrderCross.parts (record : NewOrderCross) : List Part :=
  [Part.required [53, 52, 56] record.crossID,
   Part.required [53, 52, 57] record.crossType,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [53, 53, 50] NoSide.members NoSide.encode NoSide.within record.noSide,
   Part.optional [57, 48, 52, 48] record.autoMatchOrdType,
   Part.optional [57, 48, 52, 52] record.autoMatchPrice,
   Part.optional [56, 49, 48] record.underlyingPrice,
   Part.optional [56, 55, 57] record.underlyingQty,
   Part.optional [57, 56, 49, 49] record.priceDelta,
   Part.optional [57, 56, 49, 50] record.underlyingExecutionTime,
   Part.optional [57, 56, 49, 51] record.underlyingExecutionExchange]

def NewOrderCross.tags : List (List (List UInt8)) :=
  [[[53, 52, 56]], [[53, 52, 57]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 53]], [[54, 48]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [53, 53, 50] :: NoSide.members, [[57, 48, 52, 48]], [[57, 48, 52, 52]], [[56, 49, 48]], [[56, 55, 57]], [[57, 56, 49, 49]], [[57, 56, 49, 50]], [[57, 56, 49, 51]]]

theorem NewOrderCross.shape (record : NewOrderCross) : record.parts.map Part.tags = NewOrderCross.tags := rfl

def NewOrderCross.decode (tokens : List Token) : Option NewOrderCross := do
  let crossID ← readRequired [53, 52, 56] tokens
  let crossType ← readRequired [53, 52, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noSide ← readGroup [53, 53, 50] [53, 52] NoSide.members NoSide.decode tokens
  let autoMatchOrdType ← readOptional [57, 48, 52, 48] tokens
  let autoMatchPrice ← readOptional [57, 48, 52, 52] tokens
  let underlyingPrice ← readOptional [56, 49, 48] tokens
  let underlyingQty ← readOptional [56, 55, 57] tokens
  let priceDelta ← readOptional [57, 56, 49, 49] tokens
  let underlyingExecutionTime ← readOptional [57, 56, 49, 50] tokens
  let underlyingExecutionExchange ← readOptional [57, 56, 49, 51] tokens
  pure { crossID, crossType, execInst, orderQty, ordType, price, symbol, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, noSide, autoMatchOrdType, autoMatchPrice, underlyingPrice, underlyingQty, priceDelta, underlyingExecutionTime, underlyingExecutionExchange }

theorem NewOrderCross.decode_agrees (record : NewOrderCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCross.decode tokens = some record := by
  have distinct : NewOrderCross.tags.flatten.Nodup := by decide +kernel
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have crossType := readRequired_part [53, 52, 57] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noSide := readGroup_part [53, 53, 50] [53, 52] NoSide.members NoSide.encode NoSide.within NoSide.decode NoSide.decode_encode NoSide.led record.noSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have autoMatchOrdType := readOptional_part [57, 48, 52, 48] record.autoMatchOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have autoMatchPrice := readOptional_part [57, 48, 52, 52] record.autoMatchPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have underlyingPrice := readOptional_part [56, 49, 48] record.underlyingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have underlyingQty := readOptional_part [56, 55, 57] record.underlyingQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have priceDelta := readOptional_part [57, 56, 49, 49] record.priceDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have underlyingExecutionTime := readOptional_part [57, 56, 49, 50] record.underlyingExecutionTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have underlyingExecutionExchange := readOptional_part [57, 56, 49, 51] record.underlyingExecutionExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [NewOrderCross.decode, crossID, crossType, execInst, orderQty, ordType, price, symbol, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, noSide, autoMatchOrdType, autoMatchPrice, underlyingPrice, underlyingQty, priceDelta, underlyingExecutionTime, underlyingExecutionExchange, some_bind] <;> rfl

theorem NewOrderCross.taken (record : NewOrderCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52, 56] record.crossID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 52, 57] record.crossType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
               (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSide.members NoSide.encode NoSide.within (by decide) (by decide) NoSide.taken record.noSide)
                (paired_cons pairing _ _ (paired_optional pairing [57, 48, 52, 48] record.autoMatchOrdType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 48, 52, 52] record.autoMatchPrice (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [56, 49, 48] record.underlyingPrice (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [56, 55, 57] record.underlyingQty (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 56, 49, 49] record.priceDelta (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [57, 56, 49, 50] record.underlyingExecutionTime (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [57, 56, 49, 51] record.underlyingExecutionExchange (by decide) (by decide))
                       (paired_none pairing)))))))))))))))))))))

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  legRefID : Terminated 1  -- tag 654
  legPositionEffect : Option (Terminated 1)  -- tag 564
  legCoveredOrUncovered : Option (Terminated 1)  -- tag 565

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 56] record.legCFICode,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.required [54, 53, 52] record.legRefID,
   Part.optional [53, 54, 52] record.legPositionEffect,
   Part.optional [53, 54, 53] record.legCoveredOrUncovered]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[54, 53, 52]], [[53, 54, 52]], [[53, 54, 53]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  let legPositionEffect ← readOptional [53, 54, 52] tokens
  let legCoveredOrUncovered ← readOptional [53, 54, 53] tokens
  pure { legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID, legPositionEffect, legCoveredOrUncovered }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legPositionEffect := readOptional_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legCoveredOrUncovered := readOptional_part [53, 54, 53] record.legCoveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID, legPositionEffect, legCoveredOrUncovered, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54, 48, 56] record.legCFICode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 49, 49] record.legMaturityDate (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [54, 49, 50] record.legStrikePrice (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [54, 50, 51] record.legRatioQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 50, 52] record.legSide (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [54, 53, 52] record.legRefID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 54, 52] record.legPositionEffect (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 54, 53] record.legCoveredOrUncovered (by decide) (by decide))
           (paired_none pairing)))))))))

def NoLegs.members : List (List UInt8) := NoLegs.tags.flatten

def NoLegs.encode (entry : NoLegs) : List Token := encodeParts entry.parts

theorem NoLegs.decode_encode (entry : NoLegs) : NoLegs.decode entry.encode = some entry :=
  NoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegs.within (entry : NoLegs) : ∀ token ∈ entry.encode, token.tag ∈ NoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegs.shape] at this

theorem NoLegs.led (entry : NoLegs) : Lead [54, 48, 48] entry.encode :=
  lead_parts [54, 48, 48] entry.legSymbol _ NoLegs.tags.tail rfl (by decide +kernel)

structure NewOrderMultileg where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  clientID : Option (Terminated 1)  -- tag 109
  allocAccount : Option (Terminated 1)  -- tag 79
  text : Option (Terminated 1)  -- tag 58
  mIAXExecInst : Option (Terminated 1)  -- tag 9018
  auctionID : Option (Terminated 1)  -- tag 9385
  billingMPID : Option (Terminated 1)  -- tag 9449
  noLegs : List NoLegs  -- tag 555

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [53, 56] record.text,
   Part.optional [57, 48, 49, 56] record.mIAXExecInst,
   Part.optional [57, 51, 56, 53] record.auctionID,
   Part.optional [57, 52, 52, 57] record.billingMPID,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 57]], [[55, 57]], [[53, 56]], [[57, 48, 49, 56]], [[57, 51, 56, 53]], [[57, 52, 52, 57]], [53, 53, 53] :: NoLegs.members]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let text ← readOptional [53, 56] tokens
  let mIAXExecInst ← readOptional [57, 48, 49, 56] tokens
  let auctionID ← readOptional [57, 51, 56, 53] tokens
  let billingMPID ← readOptional [57, 52, 52, 57] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, timeInForce, transactTime, securityType, customerOrFirm, clearingFirm, clearingAccount, clientID, allocAccount, text, mIAXExecInst, auctionID, billingMPID, noLegs }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have mIAXExecInst := readOptional_part [57, 48, 49, 56] record.mIAXExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 56, 53] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have billingMPID := readOptional_part [57, 52, 52, 57] record.billingMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, account, clOrdID, execInst, orderQty, ordType, price, timeInForce, transactTime, securityType, customerOrFirm, clearingFirm, clearingAccount, clientID, allocAccount, text, mIAXExecInst, auctionID, billingMPID, noLegs, some_bind] <;> rfl

theorem NewOrderMultileg.taken (record : NewOrderMultileg) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 56] record.mIAXExecInst (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 51, 56, 53] record.auctionID (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 52, 52, 57] record.billingMPID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                     (paired_none pairing)))))))))))))))))))

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  requestType : Option (Terminated 1)  -- tag 9100
  orderQty : Option (Terminated 1)  -- tag 38
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  securityType : Option (Terminated 1)  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Terminated 1  -- tag 60
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [57, 49, 48, 48] record.requestType,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[57, 49, 48, 48]], [[51, 56]], [[52, 49]], [[53, 52]], [[49, 54, 55]], [[53, 53]], [[54, 48]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let requestType ← readOptional [57, 49, 48, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  pure { clOrdID, requestType, orderQty, origClOrdID, side, securityType, symbol, transactTime, maturityMonthYear, maturityDay, putOrCall, strikePrice }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have requestType := readOptional_part [57, 49, 48, 48] record.requestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, requestType, orderQty, origClOrdID, side, securityType, symbol, transactTime, maturityMonthYear, maturityDay, putOrCall, strikePrice, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 49, 48, 48] record.requestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
              (paired_none pairing))))))))))))

structure OrderCancelReplaceRequest where
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  openClose : Option (Terminated 1)  -- tag 77
  allocAccount : Option (Terminated 1)  -- tag 79
  clientID : Option (Terminated 1)  -- tag 109
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  coveredOrUncovered : Option (Terminated 1)  -- tag 203
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 55] record.openClose,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 51] record.coveredOrUncovered,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[55, 57]], [[49, 48, 57]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 51]], [[50, 48, 52]], [[50, 48, 53]], [[52, 51, 57]], [[52, 52, 48]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let coveredOrUncovered ← readOptional [50, 48, 51] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  pure { clOrdID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, allocAccount, clientID, securityType, maturityMonthYear, putOrCall, strikePrice, coveredOrUncovered, customerOrFirm, maturityDay, clearingFirm, clearingAccount }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have coveredOrUncovered := readOptional_part [50, 48, 51] record.coveredOrUncovered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, clOrdID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, allocAccount, clientID, securityType, maturityMonthYear, putOrCall, strikePrice, coveredOrUncovered, customerOrFirm, maturityDay, clearingFirm, clearingAccount, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.openClose (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 51] record.coveredOrUncovered (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                        (paired_none pairing))))))))))))))))))))))

structure OrderCancelReplaceMultileg where
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  allocAccount : Option (Terminated 1)  -- tag 79
  text : Option (Terminated 1)  -- tag 58
  noLegs : List NoLegs  -- tag 555

def OrderCancelReplaceMultileg.parts (record : OrderCancelReplaceMultileg) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [53, 56] record.text,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def OrderCancelReplaceMultileg.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[55, 57]], [[53, 56]], [53, 53, 53] :: NoLegs.members]

theorem OrderCancelReplaceMultileg.shape (record : OrderCancelReplaceMultileg) : record.parts.map Part.tags = OrderCancelReplaceMultileg.tags := rfl

def OrderCancelReplaceMultileg.decode (tokens : List Token) : Option OrderCancelReplaceMultileg := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let text ← readOptional [53, 56] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { clOrdID, orderQty, ordType, origClOrdID, price, timeInForce, transactTime, securityType, allocAccount, text, noLegs }

theorem OrderCancelReplaceMultileg.decode_agrees (record : OrderCancelReplaceMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceMultileg.decode tokens = some record := by
  have distinct : OrderCancelReplaceMultileg.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [OrderCancelReplaceMultileg.decode, clOrdID, orderQty, ordType, origClOrdID, price, timeInForce, transactTime, securityType, allocAccount, text, noLegs, some_bind] <;> rfl

theorem OrderCancelReplaceMultileg.taken (record : OrderCancelReplaceMultileg) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
            (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
             (paired_none pairing)))))))))))

structure OrderStatusRequest where
  clOrdID : Terminated 1  -- tag 11
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167

def OrderStatusRequest.parts (record : OrderStatusRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType]

def OrderStatusRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 52]], [[53, 53]], [[49, 54, 55]]]

theorem OrderStatusRequest.shape (record : OrderStatusRequest) : record.parts.map Part.tags = OrderStatusRequest.tags := rfl

def OrderStatusRequest.decode (tokens : List Token) : Option OrderStatusRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  pure { clOrdID, side, symbol, securityType }

theorem OrderStatusRequest.decode_agrees (record : OrderStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderStatusRequest.decode tokens = some record := by
  have distinct : OrderStatusRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [OrderStatusRequest.decode, clOrdID, side, symbol, securityType, some_bind] <;> rfl

theorem OrderStatusRequest.taken (record : OrderStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
      (paired_none pairing))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | newOrderCross (header : Header) (r0 : NewOrderCross)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelReplaceMultileg (header : Header) (r0 : OrderCancelReplaceMultileg)
  | orderStatusRequest (header : Header) (r0 : OrderStatusRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCross header r0 => ⟨[51, 53], [115]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], [65, 66]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceMultileg header r0 => ⟨[51, 53], [65, 67]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderStatusRequest header r0 => ⟨[51, 53], [72]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
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
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
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
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value = [115] then
        if known (Header.tags ++ NewOrderCross.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCross.decode rest
          pure (.newOrderCross header r0)
        else none
      else if token.value = [65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
        else none
      else if token.value = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value = [65, 67] then
        if known (Header.tags ++ OrderCancelReplaceMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceMultileg.decode rest
          pure (.orderCancelReplaceMultileg header r0)
        else none
      else if token.value = [72] then
        if known (Header.tags ++ OrderStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderStatusRequest.decode rest
          pure (.orderStatusRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decode (Message.tokens (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCross.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceMultileg (header : Header) (r0 : OrderCancelReplaceMultileg) :
    Message.decode (Message.tokens (.orderCancelReplaceMultileg header r0)) = some (.orderCancelReplaceMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decode (Message.tokens (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags) rfl
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
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | newOrderCross header r0 => exact Message.decode_newOrderCross header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelReplaceMultileg header r0 => exact Message.decode_orderCancelReplaceMultileg header r0
  | orderStatusRequest header r0 => exact Message.decode_orderStatusRequest header r0

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

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decodeBytes (Message.encode (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [115]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderCross.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCross header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderMultileg.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelReplaceMultileg (header : Header) (r0 : OrderCancelReplaceMultileg) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceMultileg header r0)) = some (.orderCancelReplaceMultileg header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceMultileg.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceMultileg header r0

theorem Message.decodeBytes_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decodeBytes (Message.encode (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [72]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderStatusRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | newOrderCross header r0 => exact Message.decodeBytes_newOrderCross header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelReplaceMultileg header r0 => exact Message.decodeBytes_orderCancelReplaceMultileg header r0
  | orderStatusRequest header r0 => exact Message.decodeBytes_orderStatusRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.MiaxMiaxoptionsOrderentryFixV21DClient
