import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v4.2.2020.016, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNsmequitiesSumoordersFixV422020016Client

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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  stopPx : Option (Terminated 1)  -- tag 99
  exDestination : Option (Terminated 1)  -- tag 100
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  orderCapacity : Option (Terminated 1)  -- tag 528
  memo : Option (Terminated 1)  -- tag 5149
  sMAttribFlag : Option (Terminated 1)  -- tag 9211
  sMAIQFlag : Option (Terminated 1)  -- tag 9212
  sMBnchdFlag : Option (Terminated 1)  -- tag 9214
  blkOrdFlag : Option (Terminated 1)  -- tag 9234
  sMExecAlgorFlag : Option (Terminated 1)  -- tag 9376

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 49, 52, 57] record.memo,
   Part.optional [57, 50, 49, 49] record.sMAttribFlag,
   Part.optional [57, 50, 49, 50] record.sMAIQFlag,
   Part.optional [57, 50, 49, 52] record.sMBnchdFlag,
   Part.optional [57, 50, 51, 52] record.blkOrdFlag,
   Part.optional [57, 51, 55, 54] record.sMExecAlgorFlag]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[54, 53]], [[55, 54]], [[57, 57]], [[49, 48, 48]], [[49, 49, 48]], [[49, 49, 49]], [[50, 49, 49]], [[51, 51, 54]], [[51, 56, 56]], [[51, 56, 57]], [[53, 50, 56]], [[53, 49, 52, 57]], [[57, 50, 49, 49]], [[57, 50, 49, 50]], [[57, 50, 49, 52]], [[57, 50, 51, 52]], [[57, 51, 55, 54]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let stopPx ← readOptional [57, 57] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  let sMAttribFlag ← readOptional [57, 50, 49, 49] tokens
  let sMAIQFlag ← readOptional [57, 50, 49, 50] tokens
  let sMBnchdFlag ← readOptional [57, 50, 49, 52] tokens
  let blkOrdFlag ← readOptional [57, 50, 51, 52] tokens
  let sMExecAlgorFlag ← readOptional [57, 51, 55, 54] tokens
  pure { account, clOrdID, currency, execInst, handlInst, iDSource, orderQty, ordType, price, securityID, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, stopPx, exDestination, minQty, maxFloor, pegDifference, tradingSessionID, discretionInst, discretionOffset, orderCapacity, memo, sMAttribFlag, sMAIQFlag, sMBnchdFlag, blkOrdFlag, sMExecAlgorFlag }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have sMAttribFlag := readOptional_part [57, 50, 49, 49] record.sMAttribFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have sMAIQFlag := readOptional_part [57, 50, 49, 50] record.sMAIQFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have sMBnchdFlag := readOptional_part [57, 50, 49, 52] record.sMBnchdFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have blkOrdFlag := readOptional_part [57, 50, 51, 52] record.blkOrdFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have sMExecAlgorFlag := readOptional_part [57, 51, 55, 54] record.sMExecAlgorFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, currency, execInst, handlInst, iDSource, orderQty, ordType, price, securityID, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, stopPx, exDestination, minQty, maxFloor, pegDifference, tradingSessionID, discretionInst, discretionOffset, orderCapacity, memo, sMAttribFlag, sMAIQFlag, sMBnchdFlag, blkOrdFlag, sMExecAlgorFlag, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48] record.exDestination (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionInst (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionOffset (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [57, 50, 49, 49] record.sMAttribFlag (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 50, 49, 50] record.sMAIQFlag (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [57, 50, 49, 52] record.sMBnchdFlag (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [57, 50, 51, 52] record.blkOrdFlag (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 54] record.sMExecAlgorFlag (by decide) (by decide))
                                 (paired_none pairing)))))))))))))))))))))))))))))))

structure OrderCancelRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Option (Terminated 1)  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  cxlType : Option (Terminated 1)  -- tag 125
  memo : Option (Terminated 1)  -- tag 5149

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 50, 53] record.cxlType,
   Part.optional [53, 49, 52, 57] record.memo]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 55]], [[51, 56]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[49, 50, 53]], [[53, 49, 52, 57]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readOptional [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let cxlType ← readOptional [49, 50, 53] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { account, clOrdID, orderID, orderQty, origClOrdID, side, symbol, transactTime, symbolSfx, cxlType, memo }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cxlType := readOptional_part [49, 50, 53] record.cxlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, account, clOrdID, orderID, orderQty, origClOrdID, side, symbol, transactTime, symbolSfx, cxlType, memo, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 50, 53] record.cxlType (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
             (paired_none pairing)))))))))))

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  exDestination : Option (Terminated 1)  -- tag 100
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  pegDifference : Option (Terminated 1)  -- tag 211
  tradingSessionID : Option (Terminated 1)  -- tag 336
  memo : Option (Terminated 1)  -- tag 5149

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [53, 49, 52, 57] record.memo]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[50, 49]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[54, 53]], [[55, 54]], [[49, 48, 48]], [[49, 49, 48]], [[49, 49, 49]], [[50, 49, 49]], [[51, 51, 54]], [[53, 49, 52, 57]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { account, clOrdID, execInst, handlInst, orderID, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, exDestination, minQty, maxFloor, pegDifference, tradingSessionID, memo }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, execInst, handlInst, orderID, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, exDestination, minQty, maxFloor, pegDifference, tradingSessionID, memo, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48] record.exDestination (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
                       (paired_none pairing)))))))))))))))))))))

structure OrderStatusRequest where
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  memo : Option (Terminated 1)  -- tag 5149

def OrderStatusRequest.parts (record : OrderStatusRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [53, 49, 52, 57] record.memo]

def OrderStatusRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 52]], [[53, 53]], [[54, 53]], [[53, 49, 52, 57]]]

theorem OrderStatusRequest.shape (record : OrderStatusRequest) : record.parts.map Part.tags = OrderStatusRequest.tags := rfl

def OrderStatusRequest.decode (tokens : List Token) : Option OrderStatusRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let memo ← readOptional [53, 49, 52, 57] tokens
  pure { clOrdID, orderID, side, symbol, symbolSfx, memo }

theorem OrderStatusRequest.decode_agrees (record : OrderStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderStatusRequest.decode tokens = some record := by
  have distinct : OrderStatusRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have memo := readOptional_part [53, 49, 52, 57] record.memo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderStatusRequest.decode, clOrdID, orderID, side, symbol, symbolSfx, memo, some_bind] <;> rfl

theorem OrderStatusRequest.taken (record : OrderStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 53] record.symbolSfx (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 49, 52, 57] record.memo (by decide) (by decide))
        (paired_none pairing))))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderStatusRequest (header : Header) (r0 : OrderStatusRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderStatusRequest header r0 => ⟨[51, 53], [72]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
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
      else if token.value = [72] then
        if known (Header.tags ++ OrderStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderStatusRequest.decode rest
          pure (.orderStatusRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
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

theorem Message.decode_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decode (Message.tokens (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags) rfl
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
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderStatusRequest header r0 => exact Message.decode_orderStatusRequest header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

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

theorem Message.decodeBytes_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decodeBytes (Message.encode (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [72]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderStatusRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderStatusRequest header r0 => exact Message.decodeBytes_orderStatusRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNsmequitiesSumoordersFixV422020016Client
