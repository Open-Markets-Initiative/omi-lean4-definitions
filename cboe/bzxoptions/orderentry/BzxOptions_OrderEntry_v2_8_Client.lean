import Wire

/-!
# Chicago Board Options Exchange Order Entry v2.8, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBzxoptionsOrderentryFixV28Client

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompId : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  deliverToCompId : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 53] record.onBehalfOfCompId,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 56] record.deliverToCompId,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[53, 50]], [[49, 50, 50]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let onBehalfOfCompId ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompId ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompId := readOptional_part [49, 49, 53] record.onBehalfOfCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompId := readOptional_part [49, 50, 56] record.deliverToCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID, some_bind] <;> rfl

structure LogonandCarriedOrderRestatement where
  heartbeatInterval : Terminated 1  -- tag 108

def LogonandCarriedOrderRestatement.parts (record : LogonandCarriedOrderRestatement) : List Part :=
  [Part.required [49, 48, 56] record.heartbeatInterval]

def LogonandCarriedOrderRestatement.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]]]

theorem LogonandCarriedOrderRestatement.shape (record : LogonandCarriedOrderRestatement) : record.parts.map Part.tags = LogonandCarriedOrderRestatement.tags := rfl

def LogonandCarriedOrderRestatement.decode (tokens : List Token) : Option LogonandCarriedOrderRestatement := do
  let heartbeatInterval ← readRequired [49, 48, 56] tokens
  pure { heartbeatInterval }

theorem LogonandCarriedOrderRestatement.decode_agrees (record : LogonandCarriedOrderRestatement) (tokens : List Token)
    (agrees : ∀ tags ∈ LogonandCarriedOrderRestatement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    LogonandCarriedOrderRestatement.decode tokens = some record := by
  have distinct : LogonandCarriedOrderRestatement.tags.flatten.Nodup := by decide +kernel
  have heartbeatInterval := readRequired_part [49, 48, 56] record.heartbeatInterval tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [LogonandCarriedOrderRestatement.decode, heartbeatInterval, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
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
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

structure SequenceReset where
  newSeqNo : Terminated 1  -- tag 36
  gapFillFlag : Option (Terminated 1)  -- tag 123

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [51, 54] record.newSeqNo,
   Part.optional [49, 50, 51] record.gapFillFlag]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[51, 54]], [[49, 50, 51]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let newSeqNo ← readRequired [51, 54] tokens
  let gapFillFlag ← readOptional [49, 50, 51] tokens
  pure { newSeqNo, gapFillFlag }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have gapFillFlag := readOptional_part [49, 50, 51] record.gapFillFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SequenceReset.decode, newSeqNo, gapFillFlag, some_bind] <;> rfl

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

structure NewOrderSingle where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  openClose : Terminated 1  -- tag 77
  securityType : Terminated 1  -- tag 167
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  maxFloor : Option (Terminated 1)  -- tag 111
  displayRange : Option (Terminated 1)  -- tag 8020
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  rule80A : Option (Terminated 1)  -- tag 47
  timeInForce : Option (Terminated 1)  -- tag 59
  sessionEligibility : Option (Terminated 1)  -- tag 22017
  expireTime : Option (Terminated 1)  -- tag 126
  execInst : Option (Terminated 1)  -- tag 18
  riskReset : Option (Terminated 1)  -- tag 7692
  preventMatch : Option (Terminated 1)  -- tag 7928
  routingInst : Option (Terminated 1)  -- tag 9303
  routDeliveryMethod : Option (Terminated 1)  -- tag 9350
  routStrategy : Option (Terminated 1)  -- tag 9400
  exDestination : Option (Terminated 1)  -- tag 100
  displayIndicator : Option (Terminated 1)  -- tag 9479
  clearingFirm : Option (Terminated 1)  -- tag 439
  attributedQuote : Option (Terminated 1)  -- tag 9732
  clientID : Option (Terminated 1)  -- tag 109
  clearingOptionalData : Option (Terminated 1)  -- tag 9324
  targetPartyID : Option (Terminated 1)  -- tag 1462
  auctionID : Option (Terminated 1)  -- tag 9370
  routingFirmID : Option (Terminated 1)  -- tag 7933
  customGroupID : Option (Terminated 1)  -- tag 7699
  frequentTraderID : Option (Terminated 1)  -- tag 21097
  oRS : Option (Terminated 1)  -- tag 22003
  compression : Option (Terminated 1)  -- tag 22006
  floorRoutingInst : Option (Terminated 1)  -- tag 22303
  floorDestination : Option (Terminated 1)  -- tag 22100
  priceType : Option (Terminated 1)  -- tag 423
  orderOrigin : Option (Terminated 1)  -- tag 9465
  held : Option (Terminated 1)  -- tag 20012
  fLEXAuctionDuration : Option (Terminated 1)  -- tag 21010
  fLEXHedgeExecInst : Option (Terminated 1)  -- tag 21005
  fLEXPreFacilPrice : Option (Terminated 1)  -- tag 21008
  terminalOperatorId : Option (Terminated 1)  -- tag 22021
  additionalClientInfo : Option (Terminated 1)  -- tag 22022
  referencePrice : Option (Terminated 1)  -- tag 22025

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.required [55, 55] record.openClose,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [52, 55] record.rule80A,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [50, 50, 48, 49, 55] record.sessionEligibility,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 56] record.execInst,
   Part.optional [55, 54, 57, 50] record.riskReset,
   Part.optional [55, 57, 50, 56] record.preventMatch,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 51, 53, 48] record.routDeliveryMethod,
   Part.optional [57, 52, 48, 48] record.routStrategy,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [57, 52, 55, 57] record.displayIndicator,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [57, 55, 51, 50] record.attributedQuote,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [57, 51, 50, 52] record.clearingOptionalData,
   Part.optional [49, 52, 54, 50] record.targetPartyID,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [55, 57, 51, 51] record.routingFirmID,
   Part.optional [55, 54, 57, 57] record.customGroupID,
   Part.optional [50, 49, 48, 57, 55] record.frequentTraderID,
   Part.optional [50, 50, 48, 48, 51] record.oRS,
   Part.optional [50, 50, 48, 48, 54] record.compression,
   Part.optional [50, 50, 51, 48, 51] record.floorRoutingInst,
   Part.optional [50, 50, 49, 48, 48] record.floorDestination,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [57, 52, 54, 53] record.orderOrigin,
   Part.optional [50, 48, 48, 49, 50] record.held,
   Part.optional [50, 49, 48, 49, 48] record.fLEXAuctionDuration,
   Part.optional [50, 49, 48, 48, 53] record.fLEXHedgeExecInst,
   Part.optional [50, 49, 48, 48, 56] record.fLEXPreFacilPrice,
   Part.optional [50, 50, 48, 50, 49] record.terminalOperatorId,
   Part.optional [50, 50, 48, 50, 50] record.additionalClientInfo,
   Part.optional [50, 50, 48, 50, 53] record.referencePrice]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[53, 53]], [[53, 52]], [[51, 56]], [[49, 49, 49]], [[56, 48, 50, 48]], [[52, 48]], [[52, 52]], [[57, 57]], [[49, 49, 48]], [[52, 55]], [[53, 57]], [[50, 50, 48, 49, 55]], [[49, 50, 54]], [[49, 56]], [[55, 54, 57, 50]], [[55, 57, 50, 56]], [[57, 51, 48, 51]], [[57, 51, 53, 48]], [[57, 52, 48, 48]], [[49, 48, 48]], [[57, 52, 55, 57]], [[52, 51, 57]], [[57, 55, 51, 50]], [[49, 48, 57]], [[57, 51, 50, 52]], [[49, 52, 54, 50]], [[57, 51, 55, 48]], [[55, 57, 51, 51]], [[55, 54, 57, 57]], [[50, 49, 48, 57, 55]], [[50, 50, 48, 48, 51]], [[50, 50, 48, 48, 54]], [[50, 50, 51, 48, 51]], [[50, 50, 49, 48, 48]], [[52, 50, 51]], [[57, 52, 54, 53]], [[50, 48, 48, 49, 50]], [[50, 49, 48, 49, 48]], [[50, 49, 48, 48, 53]], [[50, 49, 48, 48, 56]], [[50, 50, 48, 50, 49]], [[50, 50, 48, 50, 50]], [[50, 50, 48, 50, 53]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let openClose ← readRequired [55, 55] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let rule80A ← readOptional [52, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let sessionEligibility ← readOptional [50, 50, 48, 49, 55] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let execInst ← readOptional [49, 56] tokens
  let riskReset ← readOptional [55, 54, 57, 50] tokens
  let preventMatch ← readOptional [55, 57, 50, 56] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let routDeliveryMethod ← readOptional [57, 51, 53, 48] tokens
  let routStrategy ← readOptional [57, 52, 48, 48] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let displayIndicator ← readOptional [57, 52, 55, 57] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let attributedQuote ← readOptional [57, 55, 51, 50] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let clearingOptionalData ← readOptional [57, 51, 50, 52] tokens
  let targetPartyID ← readOptional [49, 52, 54, 50] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let routingFirmID ← readOptional [55, 57, 51, 51] tokens
  let customGroupID ← readOptional [55, 54, 57, 57] tokens
  let frequentTraderID ← readOptional [50, 49, 48, 57, 55] tokens
  let oRS ← readOptional [50, 50, 48, 48, 51] tokens
  let compression ← readOptional [50, 50, 48, 48, 54] tokens
  let floorRoutingInst ← readOptional [50, 50, 51, 48, 51] tokens
  let floorDestination ← readOptional [50, 50, 49, 48, 48] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let orderOrigin ← readOptional [57, 52, 54, 53] tokens
  let held ← readOptional [50, 48, 48, 49, 50] tokens
  let fLEXAuctionDuration ← readOptional [50, 49, 48, 49, 48] tokens
  let fLEXHedgeExecInst ← readOptional [50, 49, 48, 48, 53] tokens
  let fLEXPreFacilPrice ← readOptional [50, 49, 48, 48, 56] tokens
  let terminalOperatorId ← readOptional [50, 50, 48, 50, 49] tokens
  let additionalClientInfo ← readOptional [50, 50, 48, 50, 50] tokens
  let referencePrice ← readOptional [50, 50, 48, 50, 53] tokens
  pure { possResend, account, clOrdId, openClose, securityType, maturityMonth, maturityDay, putOrCall, strikePrice, symbol, side, orderQty, maxFloor, displayRange, ordType, price, stopPx, minQty, rule80A, timeInForce, sessionEligibility, expireTime, execInst, riskReset, preventMatch, routingInst, routDeliveryMethod, routStrategy, exDestination, displayIndicator, clearingFirm, attributedQuote, clientID, clearingOptionalData, targetPartyID, auctionID, routingFirmID, customGroupID, frequentTraderID, oRS, compression, floorRoutingInst, floorDestination, priceType, orderOrigin, held, fLEXAuctionDuration, fLEXHedgeExecInst, fLEXPreFacilPrice, terminalOperatorId, additionalClientInfo, referencePrice }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have sessionEligibility := readOptional_part [50, 50, 48, 49, 55] record.sessionEligibility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have riskReset := readOptional_part [55, 54, 57, 50] record.riskReset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have preventMatch := readOptional_part [55, 57, 50, 56] record.preventMatch tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have routDeliveryMethod := readOptional_part [57, 51, 53, 48] record.routDeliveryMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have routStrategy := readOptional_part [57, 52, 48, 48] record.routStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have displayIndicator := readOptional_part [57, 52, 55, 57] record.displayIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have attributedQuote := readOptional_part [57, 55, 51, 50] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have clearingOptionalData := readOptional_part [57, 51, 50, 52] record.clearingOptionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have targetPartyID := readOptional_part [49, 52, 54, 50] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have routingFirmID := readOptional_part [55, 57, 51, 51] record.routingFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have customGroupID := readOptional_part [55, 54, 57, 57] record.customGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have frequentTraderID := readOptional_part [50, 49, 48, 57, 55] record.frequentTraderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have oRS := readOptional_part [50, 50, 48, 48, 51] record.oRS tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have compression := readOptional_part [50, 50, 48, 48, 54] record.compression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have floorRoutingInst := readOptional_part [50, 50, 51, 48, 51] record.floorRoutingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have floorDestination := readOptional_part [50, 50, 49, 48, 48] record.floorDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have orderOrigin := readOptional_part [57, 52, 54, 53] record.orderOrigin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have held := readOptional_part [50, 48, 48, 49, 50] record.held tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have fLEXAuctionDuration := readOptional_part [50, 49, 48, 49, 48] record.fLEXAuctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have fLEXHedgeExecInst := readOptional_part [50, 49, 48, 48, 53] record.fLEXHedgeExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have fLEXPreFacilPrice := readOptional_part [50, 49, 48, 48, 56] record.fLEXPreFacilPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have terminalOperatorId := readOptional_part [50, 50, 48, 50, 49] record.terminalOperatorId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have additionalClientInfo := readOptional_part [50, 50, 48, 50, 50] record.additionalClientInfo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have referencePrice := readOptional_part [50, 50, 48, 50, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [NewOrderSingle.decode, possResend, account, clOrdId, openClose, securityType, maturityMonth, maturityDay, putOrCall, strikePrice, symbol, side, orderQty, maxFloor, displayRange, ordType, price, stopPx, minQty, rule80A, timeInForce, sessionEligibility, expireTime, execInst, riskReset, preventMatch, routingInst, routDeliveryMethod, routStrategy, exDestination, displayIndicator, clearingFirm, attributedQuote, clientID, clearingOptionalData, targetPartyID, auctionID, routingFirmID, customGroupID, frequentTraderID, oRS, compression, floorRoutingInst, floorDestination, priceType, orderOrigin, held, fLEXAuctionDuration, fLEXHedgeExecInst, fLEXPreFacilPrice, terminalOperatorId, additionalClientInfo, referencePrice, some_bind] <;> rfl

structure NoLegs where
  legRefID : Terminated 1  -- tag 654
  legSymbol : Terminated 1  -- tag 600
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  legPrice : Option (Terminated 1)  -- tag 566
  legPositionEffect : Terminated 1  -- tag 564
  legDelta : Option (Terminated 1)  -- tag 22024

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 53, 52] record.legRefID,
   Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [53, 54, 54] record.legPrice,
   Part.required [53, 54, 52] record.legPositionEffect,
   Part.optional [50, 50, 48, 50, 52] record.legDelta]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 53, 52]], [[54, 48, 48]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[53, 54, 54]], [[53, 54, 52]], [[50, 50, 48, 50, 52]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legRefID ← readRequired [54, 53, 52] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  let legPositionEffect ← readRequired [53, 54, 52] tokens
  let legDelta ← readOptional [50, 50, 48, 50, 52] tokens
  pure { legRefID, legSymbol, legMaturityDate, legStrikePrice, legRatioQty, legSide, legPrice, legPositionEffect, legDelta }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legPositionEffect := readRequired_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legDelta := readOptional_part [50, 50, 48, 50, 52] record.legDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoLegs.decode, legRefID, legSymbol, legMaturityDate, legStrikePrice, legRatioQty, legSide, legPrice, legPositionEffect, legDelta, some_bind] <;> rfl

def NoLegs.members : List (List UInt8) := NoLegs.tags.flatten

def NoLegs.encode (entry : NoLegs) : List Token := encodeParts entry.parts

theorem NoLegs.decode_encode (entry : NoLegs) : NoLegs.decode entry.encode = some entry :=
  NoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegs.within (entry : NoLegs) : ∀ token ∈ entry.encode, token.tag ∈ NoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegs.shape] at this

theorem NoLegs.led (entry : NoLegs) : Lead [54, 53, 52] entry.encode :=
  lead_parts [54, 53, 52] entry.legRefID _ NoLegs.tags.tail rfl (by decide +kernel)

structure NewOrderMultileg where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clearingOptionalData : Option (Terminated 1)  -- tag 9324
  clOrdId : Terminated 1  -- tag 11
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  noLegs : List NoLegs  -- tag 555
  routingFirmID : Option (Terminated 1)  -- tag 7933
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  maxFloor : Option (Terminated 1)  -- tag 111
  displayRange : Option (Terminated 1)  -- tag 8020
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  drillThruProtection : Option (Terminated 1)  -- tag 6253
  routingInst : Option (Terminated 1)  -- tag 9303
  attributedQuote : Option (Terminated 1)  -- tag 9732
  clientID : Option (Terminated 1)  -- tag 109
  targetPartyID : Option (Terminated 1)  -- tag 1462
  rule80A : Option (Terminated 1)  -- tag 47
  timeInForce : Option (Terminated 1)  -- tag 59
  sessionEligibility : Option (Terminated 1)  -- tag 22017
  expireTime : Option (Terminated 1)  -- tag 126
  preventMatch : Option (Terminated 1)  -- tag 7928
  riskReset : Option (Terminated 1)  -- tag 7692
  customGroupID : Option (Terminated 1)  -- tag 7699
  priceType : Option (Terminated 1)  -- tag 423
  orderOrigin : Option (Terminated 1)  -- tag 9465
  held : Option (Terminated 1)  -- tag 20012
  fLEXAuctionDuration : Option (Terminated 1)  -- tag 21010
  fLEXHedgeExecInst : Option (Terminated 1)  -- tag 21005
  fLEXPreFacilPrice : Option (Terminated 1)  -- tag 21008
  frequentTraderID : Option (Terminated 1)  -- tag 21097
  floorRoutingInst : Option (Terminated 1)  -- tag 22303
  strategyID : Option (Terminated 1)  -- tag 22002
  oRS : Option (Terminated 1)  -- tag 22003
  comboOrder : Option (Terminated 1)  -- tag 22005
  compression : Option (Terminated 1)  -- tag 22006
  tiedHedge : Option (Terminated 1)  -- tag 22018
  equityPartyID : Option (Terminated 1)  -- tag 22008
  equityExDestination : Option (Terminated 1)  -- tag 22016
  crossInitiator : Terminated 1  -- tag 22026
  crossOnBehalfOfID : Option (Terminated 1)  -- tag 22028
  equityLegShortSell : Option (Terminated 1)  -- tag 22624
  floorDestination : Option (Terminated 1)  -- tag 22100
  terminalOperatorId : Option (Terminated 1)  -- tag 22021
  additionalClientInfo : Option (Terminated 1)  -- tag 22022
  referencePrice : Option (Terminated 1)  -- tag 22025

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.optional [57, 51, 50, 52] record.clearingOptionalData,
   Part.required [49, 49] record.clOrdId,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [55, 57, 51, 51] record.routingFirmID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [54, 50, 53, 51] record.drillThruProtection,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 55, 51, 50] record.attributedQuote,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 52, 54, 50] record.targetPartyID,
   Part.optional [52, 55] record.rule80A,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [50, 50, 48, 49, 55] record.sessionEligibility,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [55, 57, 50, 56] record.preventMatch,
   Part.optional [55, 54, 57, 50] record.riskReset,
   Part.optional [55, 54, 57, 57] record.customGroupID,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [57, 52, 54, 53] record.orderOrigin,
   Part.optional [50, 48, 48, 49, 50] record.held,
   Part.optional [50, 49, 48, 49, 48] record.fLEXAuctionDuration,
   Part.optional [50, 49, 48, 48, 53] record.fLEXHedgeExecInst,
   Part.optional [50, 49, 48, 48, 56] record.fLEXPreFacilPrice,
   Part.optional [50, 49, 48, 57, 55] record.frequentTraderID,
   Part.optional [50, 50, 51, 48, 51] record.floorRoutingInst,
   Part.optional [50, 50, 48, 48, 50] record.strategyID,
   Part.optional [50, 50, 48, 48, 51] record.oRS,
   Part.optional [50, 50, 48, 48, 53] record.comboOrder,
   Part.optional [50, 50, 48, 48, 54] record.compression,
   Part.optional [50, 50, 48, 49, 56] record.tiedHedge,
   Part.optional [50, 50, 48, 48, 56] record.equityPartyID,
   Part.optional [50, 50, 48, 49, 54] record.equityExDestination,
   Part.required [50, 50, 48, 50, 54] record.crossInitiator,
   Part.optional [50, 50, 48, 50, 56] record.crossOnBehalfOfID,
   Part.optional [50, 50, 54, 50, 52] record.equityLegShortSell,
   Part.optional [50, 50, 49, 48, 48] record.floorDestination,
   Part.optional [50, 50, 48, 50, 49] record.terminalOperatorId,
   Part.optional [50, 50, 48, 50, 50] record.additionalClientInfo,
   Part.optional [50, 50, 48, 50, 53] record.referencePrice]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[57, 51, 50, 52]], [[49, 49]], [[54, 48]], [[49, 54, 55]], [[53, 52]], [[53, 53]], [53, 53, 53] :: NoLegs.members, [[55, 57, 51, 51]], [[49, 56]], [[51, 56]], [[49, 49, 49]], [[56, 48, 50, 48]], [[52, 48]], [[52, 52]], [[52, 51, 57]], [[52, 52, 48]], [[54, 50, 53, 51]], [[57, 51, 48, 51]], [[57, 55, 51, 50]], [[49, 48, 57]], [[49, 52, 54, 50]], [[52, 55]], [[53, 57]], [[50, 50, 48, 49, 55]], [[49, 50, 54]], [[55, 57, 50, 56]], [[55, 54, 57, 50]], [[55, 54, 57, 57]], [[52, 50, 51]], [[57, 52, 54, 53]], [[50, 48, 48, 49, 50]], [[50, 49, 48, 49, 48]], [[50, 49, 48, 48, 53]], [[50, 49, 48, 48, 56]], [[50, 49, 48, 57, 55]], [[50, 50, 51, 48, 51]], [[50, 50, 48, 48, 50]], [[50, 50, 48, 48, 51]], [[50, 50, 48, 48, 53]], [[50, 50, 48, 48, 54]], [[50, 50, 48, 49, 56]], [[50, 50, 48, 48, 56]], [[50, 50, 48, 49, 54]], [[50, 50, 48, 50, 54]], [[50, 50, 48, 50, 56]], [[50, 50, 54, 50, 52]], [[50, 50, 49, 48, 48]], [[50, 50, 48, 50, 49]], [[50, 50, 48, 50, 50]], [[50, 50, 48, 50, 53]]]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clearingOptionalData ← readOptional [57, 51, 50, 52] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  let routingFirmID ← readOptional [55, 57, 51, 51] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let drillThruProtection ← readOptional [54, 50, 53, 51] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let attributedQuote ← readOptional [57, 55, 51, 50] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let targetPartyID ← readOptional [49, 52, 54, 50] tokens
  let rule80A ← readOptional [52, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let sessionEligibility ← readOptional [50, 50, 48, 49, 55] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let preventMatch ← readOptional [55, 57, 50, 56] tokens
  let riskReset ← readOptional [55, 54, 57, 50] tokens
  let customGroupID ← readOptional [55, 54, 57, 57] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let orderOrigin ← readOptional [57, 52, 54, 53] tokens
  let held ← readOptional [50, 48, 48, 49, 50] tokens
  let fLEXAuctionDuration ← readOptional [50, 49, 48, 49, 48] tokens
  let fLEXHedgeExecInst ← readOptional [50, 49, 48, 48, 53] tokens
  let fLEXPreFacilPrice ← readOptional [50, 49, 48, 48, 56] tokens
  let frequentTraderID ← readOptional [50, 49, 48, 57, 55] tokens
  let floorRoutingInst ← readOptional [50, 50, 51, 48, 51] tokens
  let strategyID ← readOptional [50, 50, 48, 48, 50] tokens
  let oRS ← readOptional [50, 50, 48, 48, 51] tokens
  let comboOrder ← readOptional [50, 50, 48, 48, 53] tokens
  let compression ← readOptional [50, 50, 48, 48, 54] tokens
  let tiedHedge ← readOptional [50, 50, 48, 49, 56] tokens
  let equityPartyID ← readOptional [50, 50, 48, 48, 56] tokens
  let equityExDestination ← readOptional [50, 50, 48, 49, 54] tokens
  let crossInitiator ← readRequired [50, 50, 48, 50, 54] tokens
  let crossOnBehalfOfID ← readOptional [50, 50, 48, 50, 56] tokens
  let equityLegShortSell ← readOptional [50, 50, 54, 50, 52] tokens
  let floorDestination ← readOptional [50, 50, 49, 48, 48] tokens
  let terminalOperatorId ← readOptional [50, 50, 48, 50, 49] tokens
  let additionalClientInfo ← readOptional [50, 50, 48, 50, 50] tokens
  let referencePrice ← readOptional [50, 50, 48, 50, 53] tokens
  pure { possResend, account, clearingOptionalData, clOrdId, transactTime, securityType, side, symbol, noLegs, routingFirmID, execInst, orderQty, maxFloor, displayRange, ordType, price, clearingFirm, clearingAccount, drillThruProtection, routingInst, attributedQuote, clientID, targetPartyID, rule80A, timeInForce, sessionEligibility, expireTime, preventMatch, riskReset, customGroupID, priceType, orderOrigin, held, fLEXAuctionDuration, fLEXHedgeExecInst, fLEXPreFacilPrice, frequentTraderID, floorRoutingInst, strategyID, oRS, comboOrder, compression, tiedHedge, equityPartyID, equityExDestination, crossInitiator, crossOnBehalfOfID, equityLegShortSell, floorDestination, terminalOperatorId, additionalClientInfo, referencePrice }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clearingOptionalData := readOptional_part [57, 51, 50, 52] record.clearingOptionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have routingFirmID := readOptional_part [55, 57, 51, 51] record.routingFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have drillThruProtection := readOptional_part [54, 50, 53, 51] record.drillThruProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have attributedQuote := readOptional_part [57, 55, 51, 50] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have targetPartyID := readOptional_part [49, 52, 54, 50] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have sessionEligibility := readOptional_part [50, 50, 48, 49, 55] record.sessionEligibility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have preventMatch := readOptional_part [55, 57, 50, 56] record.preventMatch tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have riskReset := readOptional_part [55, 54, 57, 50] record.riskReset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have customGroupID := readOptional_part [55, 54, 57, 57] record.customGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderOrigin := readOptional_part [57, 52, 54, 53] record.orderOrigin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have held := readOptional_part [50, 48, 48, 49, 50] record.held tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have fLEXAuctionDuration := readOptional_part [50, 49, 48, 49, 48] record.fLEXAuctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have fLEXHedgeExecInst := readOptional_part [50, 49, 48, 48, 53] record.fLEXHedgeExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have fLEXPreFacilPrice := readOptional_part [50, 49, 48, 48, 56] record.fLEXPreFacilPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have frequentTraderID := readOptional_part [50, 49, 48, 57, 55] record.frequentTraderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have floorRoutingInst := readOptional_part [50, 50, 51, 48, 51] record.floorRoutingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have strategyID := readOptional_part [50, 50, 48, 48, 50] record.strategyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have oRS := readOptional_part [50, 50, 48, 48, 51] record.oRS tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have comboOrder := readOptional_part [50, 50, 48, 48, 53] record.comboOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have compression := readOptional_part [50, 50, 48, 48, 54] record.compression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedge := readOptional_part [50, 50, 48, 49, 56] record.tiedHedge tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have equityPartyID := readOptional_part [50, 50, 48, 48, 56] record.equityPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have equityExDestination := readOptional_part [50, 50, 48, 49, 54] record.equityExDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have crossInitiator := readRequired_part [50, 50, 48, 50, 54] record.crossInitiator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have crossOnBehalfOfID := readOptional_part [50, 50, 48, 50, 56] record.crossOnBehalfOfID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have equityLegShortSell := readOptional_part [50, 50, 54, 50, 52] record.equityLegShortSell tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have floorDestination := readOptional_part [50, 50, 49, 48, 48] record.floorDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have terminalOperatorId := readOptional_part [50, 50, 48, 50, 49] record.terminalOperatorId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have additionalClientInfo := readOptional_part [50, 50, 48, 50, 50] record.additionalClientInfo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have referencePrice := readOptional_part [50, 50, 48, 50, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, possResend, account, clearingOptionalData, clOrdId, transactTime, securityType, side, symbol, noLegs, routingFirmID, execInst, orderQty, maxFloor, displayRange, ordType, price, clearingFirm, clearingAccount, drillThruProtection, routingInst, attributedQuote, clientID, targetPartyID, rule80A, timeInForce, sessionEligibility, expireTime, preventMatch, riskReset, customGroupID, priceType, orderOrigin, held, fLEXAuctionDuration, fLEXHedgeExecInst, fLEXPreFacilPrice, frequentTraderID, floorRoutingInst, strategyID, oRS, comboOrder, compression, tiedHedge, equityPartyID, equityExDestination, crossInitiator, crossOnBehalfOfID, equityLegShortSell, floorDestination, terminalOperatorId, additionalClientInfo, referencePrice, some_bind] <;> rfl

structure SecurityDefinitionRequest where
  clOrdId : Terminated 1  -- tag 11
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  priceType : Option (Terminated 1)  -- tag 423
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [49, 49] record.clOrdId,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [52, 50, 51] record.priceType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[54, 48]], [[49, 54, 55]], [[52, 50, 51]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let clOrdId ← readRequired [49, 49] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  pure { clOrdId, transactTime, securityType, priceType, noLegs }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, clOrdId, transactTime, securityType, priceType, noLegs, some_bind] <;> rfl

structure OrderCancelRequest where
  possResend : Option (Terminated 1)  -- tag 97
  clOrdId : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  orderId : Option (Terminated 1)  -- tag 37
  transactTime : Terminated 1  -- tag 60
  symbol : Option (Terminated 1)  -- tag 55
  openClose : Option (Terminated 1)  -- tag 77
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  massCancelInst : Option (Terminated 1)  -- tag 7700
  massCancelID : Option (Terminated 1)  -- tag 7695

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [49, 49] record.clOrdId,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderId,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [55, 55, 48, 48] record.massCancelInst,
   Part.optional [55, 54, 57, 53] record.massCancelID]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49, 49]], [[52, 49]], [[51, 55]], [[54, 48]], [[53, 53]], [[55, 55]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[51, 56]], [[55, 55, 48, 48]], [[55, 54, 57, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let possResend ← readOptional [57, 55] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let openClose ← readOptional [55, 55] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let massCancelInst ← readOptional [55, 55, 48, 48] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  pure { possResend, clOrdId, origClOrdID, orderId, transactTime, symbol, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, side, orderQty, massCancelInst, massCancelID }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have massCancelInst := readOptional_part [55, 55, 48, 48] record.massCancelInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, possResend, clOrdId, origClOrdID, orderId, transactTime, symbol, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, side, orderQty, massCancelInst, massCancelID, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  orderId : Option (Terminated 1)  -- tag 37
  transactTime : Terminated 1  -- tag 60
  symbol : Option (Terminated 1)  -- tag 55
  openClose : Option (Terminated 1)  -- tag 77
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  orderQty : Terminated 1  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  price : Terminated 1  -- tag 44
  execInst : Option (Terminated 1)  -- tag 18
  maxFloor : Option (Terminated 1)  -- tag 111
  stopPx : Option (Terminated 1)  -- tag 99
  cancelOrigOnReject : Option (Terminated 1)  -- tag 9619
  routingFirmID : Option (Terminated 1)  -- tag 7933

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderId,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [57, 57] record.stopPx,
   Part.optional [57, 54, 49, 57] record.cancelOrigOnReject,
   Part.optional [55, 57, 51, 51] record.routingFirmID]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[52, 49]], [[51, 55]], [[54, 48]], [[53, 53]], [[55, 55]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 56]], [[49, 49, 49]], [[57, 57]], [[57, 54, 49, 57]], [[55, 57, 51, 51]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let openClose ← readOptional [55, 55] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let execInst ← readOptional [49, 56] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let stopPx ← readOptional [57, 57] tokens
  let cancelOrigOnReject ← readOptional [57, 54, 49, 57] tokens
  let routingFirmID ← readOptional [55, 57, 51, 51] tokens
  pure { possResend, account, clOrdId, origClOrdID, orderId, transactTime, symbol, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, orderQty, ordType, price, execInst, maxFloor, stopPx, cancelOrigOnReject, routingFirmID }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have cancelOrigOnReject := readOptional_part [57, 54, 49, 57] record.cancelOrigOnReject tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have routingFirmID := readOptional_part [55, 57, 51, 51] record.routingFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, possResend, account, clOrdId, origClOrdID, orderId, transactTime, symbol, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, orderQty, ordType, price, execInst, maxFloor, stopPx, cancelOrigOnReject, routingFirmID, some_bind] <;> rfl

inductive Message where
  | logonandCarriedOrderRestatement (header : Header) (r0 : LogonandCarriedOrderRestatement)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)

def Message.tokens : Message → List Token
  | .logonandCarriedOrderRestatement header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [65] then
        if known (Header.tags ++ LogonandCarriedOrderRestatement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← LogonandCarriedOrderRestatement.decode rest
          pure (.logonandCarriedOrderRestatement header r0)
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
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
        else none
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else none
    else none

theorem Message.decode_logonandCarriedOrderRestatement (header : Header) (r0 : LogonandCarriedOrderRestatement) :
    Message.decode (Message.tokens (.logonandCarriedOrderRestatement header r0)) = some (.logonandCarriedOrderRestatement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (LogonandCarriedOrderRestatement.tags) rfl rfl (by decide +kernel))
  have c1 := LogonandCarriedOrderRestatement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (LogonandCarriedOrderRestatement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ LogonandCarriedOrderRestatement.tags) rfl
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

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logonandCarriedOrderRestatement header r0 => exact Message.decode_logonandCarriedOrderRestatement header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logonandCarriedOrderRestatement (header : Header) (r0 : LogonandCarriedOrderRestatement) :
    Message.decodeBytes (Message.encode (.logonandCarriedOrderRestatement header r0)) = some (.logonandCarriedOrderRestatement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ LogonandCarriedOrderRestatement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logonandCarriedOrderRestatement header r0

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

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logonandCarriedOrderRestatement header r0 => exact Message.decodeBytes_logonandCarriedOrderRestatement header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeBzxoptionsOrderentryFixV28Client
