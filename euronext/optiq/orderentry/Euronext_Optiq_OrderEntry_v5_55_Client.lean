import Wire

/-!
# Euronext Order Entry v5.55, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.EuronextOptiqOrderentryFixV555Client

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  deliverToCompID : Option (Terminated 1)  -- tag 128
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 57]], [[53, 54]], [[49, 49, 53]], [[49, 50, 56]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[51, 54, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let lastMsgSeqNumProcessed ← readOptional [51, 54, 57] tokens
  pure { msgSeqNum, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, possDupFlag, possResend, sendingTime, origSendingTime, lastMsgSeqNumProcessed }

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
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastMsgSeqNumProcessed := readOptional_part [51, 54, 57] record.lastMsgSeqNumProcessed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, possDupFlag, possResend, sendingTime, origSendingTime, lastMsgSeqNumProcessed, some_bind] <;> rfl

structure Logon where
  heartBtInt : Terminated 1  -- tag 108
  encryptMethod : Terminated 1  -- tag 98
  oEPartitionID : Terminated 1  -- tag 21019
  logicalAccessID : Terminated 1  -- tag 21021
  nextExpectedMsgSeqNum : Terminated 1  -- tag 789
  queueingIndicator : Terminated 1  -- tag 21020
  defaultApplVerID : Terminated 1  -- tag 1137
  softwareProvider : Option (Terminated 1)  -- tag 21050

def Logon.parts (record : Logon) : List Part :=
  [Part.required [49, 48, 56] record.heartBtInt,
   Part.required [57, 56] record.encryptMethod,
   Part.required [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.required [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.required [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.required [50, 49, 48, 50, 48] record.queueingIndicator,
   Part.required [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [50, 49, 48, 53, 48] record.softwareProvider]

def Logon.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]], [[57, 56]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[55, 56, 57]], [[50, 49, 48, 50, 48]], [[49, 49, 51, 55]], [[50, 49, 48, 53, 48]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let encryptMethod ← readRequired [57, 56] tokens
  let oEPartitionID ← readRequired [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readRequired [50, 49, 48, 50, 49] tokens
  let nextExpectedMsgSeqNum ← readRequired [55, 56, 57] tokens
  let queueingIndicator ← readRequired [50, 49, 48, 50, 48] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  let softwareProvider ← readOptional [50, 49, 48, 53, 48] tokens
  pure { heartBtInt, encryptMethod, oEPartitionID, logicalAccessID, nextExpectedMsgSeqNum, queueingIndicator, defaultApplVerID, softwareProvider }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEPartitionID := readRequired_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have logicalAccessID := readRequired_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readRequired_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have queueingIndicator := readRequired_part [50, 49, 48, 50, 48] record.queueingIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have softwareProvider := readOptional_part [50, 49, 48, 53, 48] record.softwareProvider tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Logon.decode, heartBtInt, encryptMethod, oEPartitionID, logicalAccessID, nextExpectedMsgSeqNum, queueingIndicator, defaultApplVerID, softwareProvider, some_bind] <;> rfl

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
  sessionStatus : Terminated 1  -- tag 1409

def Logout.parts (record : Logout) : List Part :=
  [Part.required [49, 52, 48, 57] record.sessionStatus]

def Logout.tags : List (List (List UInt8)) :=
  [[[49, 52, 48, 57]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let sessionStatus ← readRequired [49, 52, 48, 57] tokens
  pure { sessionStatus }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have sessionStatus := readRequired_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Logout.decode, sessionStatus, some_bind] <;> rfl

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

structure NewOrderSingle where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  timeInForce : Terminated 1  -- tag 59
  tradingSessionID : Option (Terminated 1)  -- tag 336
  lastCapacity : Option (Terminated 1)  -- tag 29
  nonExecClID : Option (Terminated 1)  -- tag 21081
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  sTPAggressorIndicator : Option (Terminated 1)  -- tag 21015
  disclosedQtyRandIndicator : Option (Terminated 1)  -- tag 21016
  cancelOnDisconnectionIndicator : Terminated 1  -- tag 21018
  pegPriceType : Option (Terminated 1)  -- tag 1094
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  darkExecutionInstruction : Option (Terminated 1)  -- tag 20052
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  selfMatchPreventionID : Option (Terminated 1)  -- tag 2362
  stopPx : Option (Terminated 1)  -- tag 99
  undisclosedPrice : Option (Terminated 1)  -- tag 20004
  displayQty : Option (Terminated 1)  -- tag 1138
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  undisclosedIcebergType : Option (Terminated 1)  -- tag 20005
  triggeredStopTimeInForce : Option (Terminated 1)  -- tag 20175
  quoteReqID : Option (Terminated 1)  -- tag 131
  rFQAnswerIndicator : Option (Terminated 1)  -- tag 21037
  rFQConfirmationIndicator : Option (Terminated 1)  -- tag 21038
  conditionalOrderFlag : Option (Terminated 1)  -- tag 21800
  fRMARAMPLP : Option (Terminated 1)  -- tag 21801
  iOIID : Option (Terminated 1)  -- tag 23
  side : Terminated 1  -- tag 54
  clearingInstructi : Option (Terminated 1)  -- tag 577
  text : Option (Terminated 1)  -- tag 58
  account : Option (Terminated 1)  -- tag 1
  accountCode : Terminated 1  -- tag 6399
  lPRole : Option (Terminated 1)  -- tag 20021
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  orderCapacity : Option (Terminated 1)  -- tag 528
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [53, 57] record.timeInForce,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [50, 49, 48, 56, 49] record.nonExecClID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 49, 48, 49, 53] record.sTPAggressorIndicator,
   Part.optional [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator,
   Part.required [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [50, 51, 54, 50] record.selfMatchPreventionID,
   Part.optional [57, 57] record.stopPx,
   Part.optional [50, 48, 48, 48, 52] record.undisclosedPrice,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [50, 48, 48, 48, 53] record.undisclosedIcebergType,
   Part.optional [50, 48, 49, 55, 53] record.triggeredStopTimeInForce,
   Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [50, 49, 48, 51, 55] record.rFQAnswerIndicator,
   Part.optional [50, 49, 48, 51, 56] record.rFQConfirmationIndicator,
   Part.optional [50, 49, 56, 48, 48] record.conditionalOrderFlag,
   Part.optional [50, 49, 56, 48, 49] record.fRMARAMPLP,
   Part.optional [50, 51] record.iOIID,
   Part.required [53, 52] record.side,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [53, 56] record.text,
   Part.optional [49] record.account,
   Part.required [54, 51, 57, 57] record.accountCode,
   Part.optional [50, 48, 48, 50, 49] record.lPRole,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[52, 52]], [[51, 56]], [[52, 48]], [[53, 57]], [[51, 51, 54]], [[50, 57]], [[50, 49, 48, 56, 49]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 49, 48, 49, 53]], [[50, 49, 48, 49, 54]], [[50, 49, 48, 49, 56]], [[49, 48, 57, 52]], [[50, 49, 49]], [[50, 48, 48, 53, 50]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 51, 54, 50]], [[57, 57]], [[50, 48, 48, 48, 52]], [[49, 49, 51, 56]], [[49, 49, 48]], [[49, 50, 54]], [[52, 51, 50]], [[50, 48, 48, 48, 53]], [[50, 48, 49, 55, 53]], [[49, 51, 49]], [[50, 49, 48, 51, 55]], [[50, 49, 48, 51, 56]], [[50, 49, 56, 48, 48]], [[50, 49, 56, 48, 49]], [[50, 51]], [[53, 52]], [[53, 55, 55]], [[53, 56]], [[49]], [[54, 51, 57, 57]], [[50, 48, 48, 50, 49]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[53, 50, 56]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let nonExecClID ← readOptional [50, 49, 48, 56, 49] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let sTPAggressorIndicator ← readOptional [50, 49, 48, 49, 53] tokens
  let disclosedQtyRandIndicator ← readOptional [50, 49, 48, 49, 54] tokens
  let cancelOnDisconnectionIndicator ← readRequired [50, 49, 48, 49, 56] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let darkExecutionInstruction ← readOptional [50, 48, 48, 53, 50] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let selfMatchPreventionID ← readOptional [50, 51, 54, 50] tokens
  let stopPx ← readOptional [57, 57] tokens
  let undisclosedPrice ← readOptional [50, 48, 48, 48, 52] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let undisclosedIcebergType ← readOptional [50, 48, 48, 48, 53] tokens
  let triggeredStopTimeInForce ← readOptional [50, 48, 49, 55, 53] tokens
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let rFQAnswerIndicator ← readOptional [50, 49, 48, 51, 55] tokens
  let rFQConfirmationIndicator ← readOptional [50, 49, 48, 51, 56] tokens
  let conditionalOrderFlag ← readOptional [50, 49, 56, 48, 48] tokens
  let fRMARAMPLP ← readOptional [50, 49, 56, 48, 49] tokens
  let iOIID ← readOptional [50, 51] tokens
  let side ← readRequired [53, 52] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let account ← readOptional [49] tokens
  let accountCode ← readRequired [54, 51, 57, 57] tokens
  let lPRole ← readOptional [50, 48, 48, 50, 49] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  pure { transactTime, clOrdID, securityID, securityIDSource, eMM, price, orderQty, ordType, timeInForce, tradingSessionID, lastCapacity, nonExecClID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, sTPAggressorIndicator, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, darkExecutionInstruction, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, selfMatchPreventionID, stopPx, undisclosedPrice, displayQty, minQty, expireTime, expireDate, undisclosedIcebergType, triggeredStopTimeInForce, quoteReqID, rFQAnswerIndicator, rFQConfirmationIndicator, conditionalOrderFlag, fRMARAMPLP, iOIID, side, clearingInstructi, text, account, accountCode, lPRole, technicalOrdType, postingAction, orderCapacity, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have nonExecClID := readOptional_part [50, 49, 48, 56, 49] record.nonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have sTPAggressorIndicator := readOptional_part [50, 49, 48, 49, 53] record.sTPAggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have disclosedQtyRandIndicator := readOptional_part [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cancelOnDisconnectionIndicator := readRequired_part [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have darkExecutionInstruction := readOptional_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 51, 54, 50] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have undisclosedPrice := readOptional_part [50, 48, 48, 48, 52] record.undisclosedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have undisclosedIcebergType := readOptional_part [50, 48, 48, 48, 53] record.undisclosedIcebergType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have triggeredStopTimeInForce := readOptional_part [50, 48, 49, 55, 53] record.triggeredStopTimeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have rFQAnswerIndicator := readOptional_part [50, 49, 48, 51, 55] record.rFQAnswerIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have rFQConfirmationIndicator := readOptional_part [50, 49, 48, 51, 56] record.rFQConfirmationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have conditionalOrderFlag := readOptional_part [50, 49, 56, 48, 48] record.conditionalOrderFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have fRMARAMPLP := readOptional_part [50, 49, 56, 48, 49] record.fRMARAMPLP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have iOIID := readOptional_part [50, 51] record.iOIID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have accountCode := readRequired_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have lPRole := readOptional_part [50, 48, 48, 50, 49] record.lPRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  simp only [NewOrderSingle.decode, transactTime, clOrdID, securityID, securityIDSource, eMM, price, orderQty, ordType, timeInForce, tradingSessionID, lastCapacity, nonExecClID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, sTPAggressorIndicator, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, darkExecutionInstruction, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, selfMatchPreventionID, stopPx, undisclosedPrice, displayQty, minQty, expireTime, expireDate, undisclosedIcebergType, triggeredStopTimeInForce, quoteReqID, rFQAnswerIndicator, rFQConfirmationIndicator, conditionalOrderFlag, fRMARAMPLP, iOIID, side, clearingInstructi, text, account, accountCode, lPRole, technicalOrdType, postingAction, orderCapacity, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, some_bind] <;> rfl

structure MassQuote where
  quoteID : Terminated 1  -- tag 117
  lastCapacity : Terminated 1  -- tag 29
  accountCode : Terminated 1  -- tag 6399
  lPRole : Terminated 1  -- tag 20021
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  rFEAnswer : Terminated 1  -- tag 20022
  clearingInstructi : Option (Terminated 1)  -- tag 577
  text : Option (Terminated 1)  -- tag 58
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  account : Option (Terminated 1)  -- tag 1
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  quoteSetID : Terminated 1  -- tag 302
  noQuoteEntries : Terminated 1  -- tag 295
  quoteEntryID : Terminated 1  -- tag 299
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  bidSize : Option (Terminated 1)  -- tag 134
  bidPx : Option (Terminated 1)  -- tag 132
  offerSize : Option (Terminated 1)  -- tag 135
  offerPx : Option (Terminated 1)  -- tag 133

def MassQuote.parts (record : MassQuote) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [50, 57] record.lastCapacity,
   Part.required [54, 51, 57, 57] record.accountCode,
   Part.required [50, 48, 48, 50, 49] record.lPRole,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [50, 48, 48, 50, 50] record.rFEAnswer,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [53, 56] record.text,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [49] record.account,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.required [51, 48, 50] record.quoteSetID,
   Part.required [50, 57, 53] record.noQuoteEntries,
   Part.required [50, 57, 57] record.quoteEntryID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [49, 51, 51] record.offerPx]

def MassQuote.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[50, 57]], [[54, 51, 57, 57]], [[50, 48, 48, 50, 49]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 48, 48, 50, 50]], [[53, 55, 55]], [[53, 56]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[53, 51, 57]], [[53, 50, 52]], [[53, 51, 56]], [[50, 51, 56, 52]], [[49]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[51, 48, 50]], [[50, 57, 53]], [[50, 57, 57]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[49, 51, 52]], [[49, 51, 50]], [[49, 51, 53]], [[49, 51, 51]]]

theorem MassQuote.shape (record : MassQuote) : record.parts.map Part.tags = MassQuote.tags := rfl

def MassQuote.decode (tokens : List Token) : Option MassQuote := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let lastCapacity ← readRequired [50, 57] tokens
  let accountCode ← readRequired [54, 51, 57, 57] tokens
  let lPRole ← readRequired [50, 48, 48, 50, 49] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let rFEAnswer ← readRequired [50, 48, 48, 50, 50] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let account ← readOptional [49] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let quoteSetID ← readRequired [51, 48, 50] tokens
  let noQuoteEntries ← readRequired [50, 57, 53] tokens
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  pure { quoteID, lastCapacity, accountCode, lPRole, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, rFEAnswer, clearingInstructi, text, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyRole, nestedPartyRoleQualifier, account, technicalOrdType, postingAction, quoteSetID, noQuoteEntries, quoteEntryID, securityID, securityIDSource, eMM, bidSize, bidPx, offerSize, offerPx }

theorem MassQuote.decode_agrees (record : MassQuote) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuote.decode tokens = some record := by
  have distinct : MassQuote.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastCapacity := readRequired_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have accountCode := readRequired_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lPRole := readRequired_part [50, 48, 48, 50, 49] record.lPRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have rFEAnswer := readRequired_part [50, 48, 48, 50, 50] record.rFEAnswer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have quoteSetID := readRequired_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noQuoteEntries := readRequired_part [50, 57, 53] record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [MassQuote.decode, quoteID, lastCapacity, accountCode, lPRole, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, rFEAnswer, clearingInstructi, text, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyRole, nestedPartyRoleQualifier, account, technicalOrdType, postingAction, quoteSetID, noQuoteEntries, quoteEntryID, securityID, securityIDSource, eMM, bidSize, bidPx, offerSize, offerPx, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Terminated 1  -- tag 54
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  transactTime : Terminated 1  -- tag 60
  ordType : Terminated 1  -- tag 40
  pegPriceType : Option (Terminated 1)  -- tag 1094
  orderCategory : Option (Terminated 1)  -- tag 21041

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [54, 48] record.transactTime,
   Part.required [52, 48] record.ordType,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55]], [[52, 49]], [[53, 52]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[54, 48]], [[52, 48]], [[49, 48, 57, 52]], [[50, 49, 48, 52, 49]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let ordType ← readRequired [52, 48] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  pure { clOrdID, securityID, securityIDSource, eMM, orderID, origClOrdID, side, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, transactTime, ordType, pegPriceType, orderCategory }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, securityID, securityIDSource, eMM, orderID, origClOrdID, side, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, transactTime, ordType, pegPriceType, orderCategory, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  price : Option (Terminated 1)  -- tag 44
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  side : Terminated 1  -- tag 54
  timeInForce : Terminated 1  -- tag 59
  lPRole : Option (Terminated 1)  -- tag 20021
  accountCode : Option (Terminated 1)  -- tag 6399
  sTPAggressorIndicator : Option (Terminated 1)  -- tag 21015
  disclosedQtyRandIndicator : Option (Terminated 1)  -- tag 21016
  cancelOnDisconnectionIndicator : Terminated 1  -- tag 21018
  pegPriceType : Option (Terminated 1)  -- tag 1094
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  darkExecutionInstruction : Option (Terminated 1)  -- tag 20052
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  selfMatchPreventionID : Option (Terminated 1)  -- tag 2362
  text : Option (Terminated 1)  -- tag 58
  stopPx : Option (Terminated 1)  -- tag 99
  undisclosedPrice : Option (Terminated 1)  -- tag 20004
  displayQty : Option (Terminated 1)  -- tag 1138
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  tradingSessionID : Option (Terminated 1)  -- tag 336
  triggeredStopTimeInForce : Option (Terminated 1)  -- tag 20175
  undisclosedIcebergType : Option (Terminated 1)  -- tag 20005
  account : Option (Terminated 1)  -- tag 1
  longClientID : Option (Terminated 1)  -- tag 21804
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  clearingInstructi : Option (Terminated 1)  -- tag 577
  confirmFlag : Option (Terminated 1)  -- tag 9930
  conditionalOrderFlag : Option (Terminated 1)  -- tag 21800
  fRMARAMPLP : Option (Terminated 1)  -- tag 21801

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [53, 52] record.side,
   Part.required [53, 57] record.timeInForce,
   Part.optional [50, 48, 48, 50, 49] record.lPRole,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.optional [50, 49, 48, 49, 53] record.sTPAggressorIndicator,
   Part.optional [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator,
   Part.required [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [50, 51, 54, 50] record.selfMatchPreventionID,
   Part.optional [53, 56] record.text,
   Part.optional [57, 57] record.stopPx,
   Part.optional [50, 48, 48, 48, 52] record.undisclosedPrice,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [50, 48, 49, 55, 53] record.triggeredStopTimeInForce,
   Part.optional [50, 48, 48, 48, 53] record.undisclosedIcebergType,
   Part.optional [49] record.account,
   Part.optional [50, 49, 56, 48, 52] record.longClientID,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [57, 57, 51, 48] record.confirmFlag,
   Part.optional [50, 49, 56, 48, 48] record.conditionalOrderFlag,
   Part.optional [50, 49, 56, 48, 49] record.fRMARAMPLP]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55]], [[52, 49]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[52, 52]], [[51, 56]], [[52, 48]], [[53, 52]], [[53, 57]], [[50, 48, 48, 50, 49]], [[54, 51, 57, 57]], [[50, 49, 48, 49, 53]], [[50, 49, 48, 49, 54]], [[50, 49, 48, 49, 56]], [[49, 48, 57, 52]], [[50, 49, 49]], [[50, 48, 48, 53, 50]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 51, 54, 50]], [[53, 56]], [[57, 57]], [[50, 48, 48, 48, 52]], [[49, 49, 51, 56]], [[49, 50, 54]], [[52, 51, 50]], [[51, 51, 54]], [[50, 48, 49, 55, 53]], [[50, 48, 48, 48, 53]], [[49]], [[50, 49, 56, 48, 52]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[53, 55, 55]], [[57, 57, 51, 48]], [[50, 49, 56, 48, 48]], [[50, 49, 56, 48, 49]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let side ← readRequired [53, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let lPRole ← readOptional [50, 48, 48, 50, 49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let sTPAggressorIndicator ← readOptional [50, 49, 48, 49, 53] tokens
  let disclosedQtyRandIndicator ← readOptional [50, 49, 48, 49, 54] tokens
  let cancelOnDisconnectionIndicator ← readRequired [50, 49, 48, 49, 56] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let darkExecutionInstruction ← readOptional [50, 48, 48, 53, 50] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let selfMatchPreventionID ← readOptional [50, 51, 54, 50] tokens
  let text ← readOptional [53, 56] tokens
  let stopPx ← readOptional [57, 57] tokens
  let undisclosedPrice ← readOptional [50, 48, 48, 48, 52] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let triggeredStopTimeInForce ← readOptional [50, 48, 49, 55, 53] tokens
  let undisclosedIcebergType ← readOptional [50, 48, 48, 48, 53] tokens
  let account ← readOptional [49] tokens
  let longClientID ← readOptional [50, 49, 56, 48, 52] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let confirmFlag ← readOptional [57, 57, 51, 48] tokens
  let conditionalOrderFlag ← readOptional [50, 49, 56, 48, 48] tokens
  let fRMARAMPLP ← readOptional [50, 49, 56, 48, 49] tokens
  pure { transactTime, clOrdID, securityID, securityIDSource, eMM, orderID, origClOrdID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, price, orderQty, ordType, side, timeInForce, lPRole, accountCode, sTPAggressorIndicator, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, darkExecutionInstruction, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, selfMatchPreventionID, text, stopPx, undisclosedPrice, displayQty, expireTime, expireDate, tradingSessionID, triggeredStopTimeInForce, undisclosedIcebergType, account, longClientID, technicalOrdType, postingAction, clearingInstructi, confirmFlag, conditionalOrderFlag, fRMARAMPLP }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have lPRole := readOptional_part [50, 48, 48, 50, 49] record.lPRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have sTPAggressorIndicator := readOptional_part [50, 49, 48, 49, 53] record.sTPAggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have disclosedQtyRandIndicator := readOptional_part [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have cancelOnDisconnectionIndicator := readRequired_part [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have darkExecutionInstruction := readOptional_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 51, 54, 50] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have undisclosedPrice := readOptional_part [50, 48, 48, 48, 52] record.undisclosedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have triggeredStopTimeInForce := readOptional_part [50, 48, 49, 55, 53] record.triggeredStopTimeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have undisclosedIcebergType := readOptional_part [50, 48, 48, 48, 53] record.undisclosedIcebergType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have longClientID := readOptional_part [50, 49, 56, 48, 52] record.longClientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have confirmFlag := readOptional_part [57, 57, 51, 48] record.confirmFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have conditionalOrderFlag := readOptional_part [50, 49, 56, 48, 48] record.conditionalOrderFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have fRMARAMPLP := readOptional_part [50, 49, 56, 48, 49] record.fRMARAMPLP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, transactTime, clOrdID, securityID, securityIDSource, eMM, orderID, origClOrdID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, price, orderQty, ordType, side, timeInForce, lPRole, accountCode, sTPAggressorIndicator, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, darkExecutionInstruction, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, selfMatchPreventionID, text, stopPx, undisclosedPrice, displayQty, expireTime, expireDate, tradingSessionID, triggeredStopTimeInForce, undisclosedIcebergType, account, longClientID, technicalOrdType, postingAction, clearingInstructi, confirmFlag, conditionalOrderFlag, fRMARAMPLP, some_bind] <;> rfl

structure OwnershipRequest where
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  eMM : Terminated 1  -- tag 20020
  oEPartitionID : Option (Terminated 1)  -- tag 21019
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  orderCategory : Option (Terminated 1)  -- tag 21041

def OwnershipRequest.parts (record : OwnershipRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory]

def OwnershipRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[52, 49]], [[52, 56]], [[50, 50]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 48, 48, 50, 48]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[50, 49, 48, 52, 49]]]

theorem OwnershipRequest.shape (record : OwnershipRequest) : record.parts.map Part.tags = OwnershipRequest.tags := rfl

def OwnershipRequest.decode (tokens : List Token) : Option OwnershipRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  pure { clOrdID, orderID, origClOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, oEPartitionID, logicalAccessID, orderCategory }

theorem OwnershipRequest.decode_agrees (record : OwnershipRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OwnershipRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OwnershipRequest.decode tokens = some record := by
  have distinct : OwnershipRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [OwnershipRequest.decode, clOrdID, orderID, origClOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, oEPartitionID, logicalAccessID, orderCategory, some_bind] <;> rfl

structure QuoteRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  side : Option (Terminated 1)  -- tag 54
  orderQty : Terminated 1  -- tag 38
  darkExecutionInstruction : Option (Terminated 1)  -- tag 20052
  minQty : Option (Terminated 1)  -- tag 110
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  accountCode : Option (Terminated 1)  -- tag 6399
  quoteType : Option (Terminated 1)  -- tag 537
  exposureDuration : Option (Terminated 1)  -- tag 1629
  numOfCompetitors : Option (Terminated 1)  -- tag 1913
  price : Option (Terminated 1)  -- tag 44
  lastCapacity : Option (Terminated 1)  -- tag 29
  clearingInstructi : Option (Terminated 1)  -- tag 577
  text : Option (Terminated 1)  -- tag 58
  account : Option (Terminated 1)  -- tag 1
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  orderOrigination : Option (Terminated 1)  -- tag 1724
  postingAction : Option (Terminated 1)  -- tag 7443
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.optional [53, 51, 55] record.quoteType,
   Part.optional [49, 54, 50, 57] record.exposureDuration,
   Part.optional [49, 57, 49, 51] record.numOfCompetitors,
   Part.optional [52, 52] record.price,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [53, 56] record.text,
   Part.optional [49] record.account,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[53, 52]], [[51, 56]], [[50, 48, 48, 53, 50]], [[49, 49, 48]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[54, 51, 57, 57]], [[53, 51, 55]], [[49, 54, 50, 57]], [[49, 57, 49, 51]], [[52, 52]], [[50, 57]], [[53, 55, 55]], [[53, 56]], [[49]], [[57, 57, 52, 49]], [[49, 55, 50, 52]], [[55, 52, 52, 51]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let darkExecutionInstruction ← readOptional [50, 48, 48, 53, 50] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let quoteType ← readOptional [53, 51, 55] tokens
  let exposureDuration ← readOptional [49, 54, 50, 57] tokens
  let numOfCompetitors ← readOptional [49, 57, 49, 51] tokens
  let price ← readOptional [52, 52] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let account ← readOptional [49] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  pure { transactTime, clOrdID, securityID, securityIDSource, eMM, side, orderQty, darkExecutionInstruction, minQty, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, accountCode, quoteType, exposureDuration, numOfCompetitors, price, lastCapacity, clearingInstructi, text, account, technicalOrdType, orderOrigination, postingAction, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noOrderAttribut, orderAttributeTy, orderAttributeValue }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have darkExecutionInstruction := readOptional_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have quoteType := readOptional_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have exposureDuration := readOptional_part [49, 54, 50, 57] record.exposureDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have numOfCompetitors := readOptional_part [49, 57, 49, 51] record.numOfCompetitors tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  simp only [QuoteRequest.decode, transactTime, clOrdID, securityID, securityIDSource, eMM, side, orderQty, darkExecutionInstruction, minQty, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, accountCode, quoteType, exposureDuration, numOfCompetitors, price, lastCapacity, clearingInstructi, text, account, technicalOrdType, orderOrigination, postingAction, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noOrderAttribut, orderAttributeTy, orderAttributeValue, some_bind] <;> rfl

structure PriceInput where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  eMM : Terminated 1  -- tag 20020
  price : Option (Terminated 1)  -- tag 44
  inputPxType : Terminated 1  -- tag 9950

def PriceInput.parts (record : PriceInput) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [52, 52] record.price,
   Part.required [57, 57, 53, 48] record.inputPxType]

def PriceInput.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 48, 48, 50, 48]], [[52, 52]], [[57, 57, 53, 48]]]

theorem PriceInput.shape (record : PriceInput) : record.parts.map Part.tags = PriceInput.tags := rfl

def PriceInput.decode (tokens : List Token) : Option PriceInput := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let price ← readOptional [52, 52] tokens
  let inputPxType ← readRequired [57, 57, 53, 48] tokens
  pure { clOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, price, inputPxType }

theorem PriceInput.decode_agrees (record : PriceInput) (tokens : List Token)
    (agrees : ∀ tags ∈ PriceInput.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PriceInput.decode tokens = some record := by
  have distinct : PriceInput.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have inputPxType := readRequired_part [57, 57, 53, 48] record.inputPxType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [PriceInput.decode, clOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, price, inputPxType, some_bind] <;> rfl

structure LiquidityProviderCommand where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  eMM : Terminated 1  -- tag 20020
  lPActionCode : Terminated 1  -- tag 10076

def LiquidityProviderCommand.parts (record : LiquidityProviderCommand) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [49, 48, 48, 55, 54] record.lPActionCode]

def LiquidityProviderCommand.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 48, 48, 50, 48]], [[49, 48, 48, 55, 54]]]

theorem LiquidityProviderCommand.shape (record : LiquidityProviderCommand) : record.parts.map Part.tags = LiquidityProviderCommand.tags := rfl

def LiquidityProviderCommand.decode (tokens : List Token) : Option LiquidityProviderCommand := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let lPActionCode ← readRequired [49, 48, 48, 55, 54] tokens
  pure { clOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, lPActionCode }

theorem LiquidityProviderCommand.decode_agrees (record : LiquidityProviderCommand) (tokens : List Token)
    (agrees : ∀ tags ∈ LiquidityProviderCommand.tags, select tags tokens = select tags (encodeParts record.parts)) :
    LiquidityProviderCommand.decode tokens = some record := by
  have distinct : LiquidityProviderCommand.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lPActionCode := readRequired_part [49, 48, 48, 55, 54] record.lPActionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [LiquidityProviderCommand.decode, clOrdID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, lPActionCode, some_bind] <;> rfl

structure OrderMassStatusRequest where
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  massStatusReqID : Terminated 1  -- tag 584
  massStatusReqType : Terminated 1  -- tag 585
  eMM : Terminated 1  -- tag 20020
  orderCategory : Option (Terminated 1)  -- tag 21041

def OrderMassStatusRequest.parts (record : OrderMassStatusRequest) : List Part :=
  [Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [53, 56, 52] record.massStatusReqID,
   Part.required [53, 56, 53] record.massStatusReqType,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory]

def OrderMassStatusRequest.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[50, 50]], [[51, 55]], [[52, 49]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[53, 56, 52]], [[53, 56, 53]], [[50, 48, 48, 50, 48]], [[50, 49, 48, 52, 49]]]

theorem OrderMassStatusRequest.shape (record : OrderMassStatusRequest) : record.parts.map Part.tags = OrderMassStatusRequest.tags := rfl

def OrderMassStatusRequest.decode (tokens : List Token) : Option OrderMassStatusRequest := do
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let massStatusReqID ← readRequired [53, 56, 52] tokens
  let massStatusReqType ← readRequired [53, 56, 53] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  pure { securityID, securityIDSource, orderID, origClOrdID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, massStatusReqID, massStatusReqType, eMM, orderCategory }

theorem OrderMassStatusRequest.decode_agrees (record : OrderMassStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassStatusRequest.decode tokens = some record := by
  have distinct : OrderMassStatusRequest.tags.flatten.Nodup := by decide +kernel
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have massStatusReqID := readRequired_part [53, 56, 52] record.massStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have massStatusReqType := readRequired_part [53, 56, 53] record.massStatusReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [OrderMassStatusRequest.decode, securityID, securityIDSource, orderID, origClOrdID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noOrderAttribut, orderAttributeTy, orderAttributeValue, massStatusReqID, massStatusReqType, eMM, orderCategory, some_bind] <;> rfl

structure OrderMassCancelRequest where
  transactTime : Terminated 1  -- tag 60
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  classID : Option (Terminated 1)  -- tag 9945
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  targetPartyID : Option (Terminated 1)  -- tag 21095
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  eMM : Option (Terminated 1)  -- tag 20020
  side : Option (Terminated 1)  -- tag 54
  oEPartitionID : Option (Terminated 1)  -- tag 21019
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  accountCode : Option (Terminated 1)  -- tag 6399
  orderCategory : Option (Terminated 1)  -- tag 21041

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [57, 57, 52, 53] record.classID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [53, 52] record.side,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[49, 49]], [[53, 51, 48]], [[57, 57, 52, 53]], [[52, 56]], [[50, 50]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 49, 48, 57, 53]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 48, 48, 50, 48]], [[53, 52]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[54, 51, 57, 57]], [[50, 49, 48, 52, 49]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let transactTime ← readRequired [54, 48] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let classID ← readOptional [57, 57, 52, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let side ← readOptional [53, 52] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  pure { transactTime, clOrdID, massCancelRequestType, classID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, targetPartyID, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, side, oEPartitionID, logicalAccessID, accountCode, orderCategory }

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
  have classID := readOptional_part [57, 57, 52, 53] record.classID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, transactTime, clOrdID, massCancelRequestType, classID, securityID, securityIDSource, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, targetPartyID, noOrderAttribut, orderAttributeTy, orderAttributeValue, eMM, side, oEPartitionID, logicalAccessID, accountCode, orderCategory, some_bind] <;> rfl

structure SecurityDefinitionRequest where
  securityReqID : Terminated 1  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityType : Terminated 1  -- tag 167
  securitySubType : Terminated 1  -- tag 762
  noLegs : Terminated 1  -- tag 555
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Terminated 1  -- tag 602
  legSecurityIDSo : Terminated 1  -- tag 603
  legSecurityType : Terminated 1  -- tag 609
  legLastTradingDate : Option (Terminated 1)  -- tag 21092
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatio : Terminated 1  -- tag 21091
  legSide : Terminated 1  -- tag 624
  legPutOrCall : Option (Terminated 1)  -- tag 1358
  legPrice : Option (Terminated 1)  -- tag 566

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [49, 54, 55] record.securityType,
   Part.required [55, 54, 50] record.securitySubType,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 50] record.legSecurityID,
   Part.required [54, 48, 51] record.legSecurityIDSo,
   Part.required [54, 48, 57] record.legSecurityType,
   Part.optional [50, 49, 48, 57, 50] record.legLastTradingDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [50, 49, 48, 57, 49] record.legRatio,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [49, 51, 53, 56] record.legPutOrCall,
   Part.optional [53, 54, 54] record.legPrice]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[52, 56]], [[50, 50]], [[49, 54, 55]], [[55, 54, 50]], [[53, 53, 53]], [[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 48, 57]], [[50, 49, 48, 57, 50]], [[54, 49, 50]], [[50, 49, 48, 57, 49]], [[54, 50, 52]], [[49, 51, 53, 56]], [[53, 54, 54]]]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securitySubType ← readRequired [55, 54, 50] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readRequired [54, 48, 50] tokens
  let legSecurityIDSo ← readRequired [54, 48, 51] tokens
  let legSecurityType ← readRequired [54, 48, 57] tokens
  let legLastTradingDate ← readOptional [50, 49, 48, 57, 50] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatio ← readRequired [50, 49, 48, 57, 49] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legPutOrCall ← readOptional [49, 51, 53, 56] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  pure { securityReqID, securityRequestType, securityID, securityIDSource, securityType, securitySubType, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legSecurityType, legLastTradingDate, legStrikePrice, legRatio, legSide, legPutOrCall, legPrice }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securitySubType := readRequired_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legSecurityID := readRequired_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have legSecurityIDSo := readRequired_part [54, 48, 51] record.legSecurityIDSo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have legSecurityType := readRequired_part [54, 48, 57] record.legSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have legLastTradingDate := readOptional_part [50, 49, 48, 57, 50] record.legLastTradingDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have legRatio := readRequired_part [50, 49, 48, 57, 49] record.legRatio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have legPutOrCall := readOptional_part [49, 51, 53, 56] record.legPutOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, securityID, securityIDSource, securityType, securitySubType, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legSecurityType, legLastTradingDate, legStrikePrice, legRatio, legSide, legPutOrCall, legPrice, some_bind] <;> rfl

structure NewWholesaleOrder where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  wholesaleTradeType : Terminated 1  -- tag 21083
  lISTransactionID : Option (Terminated 1)  -- tag 21085
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  price : Terminated 1  -- tag 44
  quantity : Terminated 1  -- tag 53
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  wholesaleSide : Terminated 1  -- tag 21082
  eSCBMembership : Option (Terminated 1)  -- tag 21096
  messagePriceNotation : Option (Terminated 1)  -- tag 21803
  tradePublicationType : Option (Terminated 1)  -- tag 1390
  noLegs : Terminated 1  -- tag 555
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Terminated 1  -- tag 602
  legSecurityIDSo : Option (Terminated 1)  -- tag 603
  legSecurityType : Terminated 1  -- tag 609
  legLastTradingDate : Option (Terminated 1)  -- tag 21092
  legPutOrCall : Option (Terminated 1)  -- tag 1358
  legPrice : Terminated 1  -- tag 566
  legSide : Option (Terminated 1)  -- tag 624
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135
  bidNonExecClID : Option (Terminated 1)  -- tag 21089
  offerNonExecClID : Option (Terminated 1)  -- tag 21090
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatio : Option (Terminated 1)  -- tag 21091
  noSides : Option (Terminated 1)  -- tag 552
  side : Terminated 1  -- tag 54
  clearingInstructi : Option (Terminated 1)  -- tag 577
  text : Option (Terminated 1)  -- tag 58
  account : Option (Terminated 1)  -- tag 1
  accountCode : Terminated 1  -- tag 6399
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  lastCapacity : Terminated 1  -- tag 29
  longClientID : Option (Terminated 1)  -- tag 21804
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  noNestedOrderAttributes : Option (Terminated 1)  -- tag 21086
  nestedOrderAttributeType : Option (Terminated 1)  -- tag 21087
  nestedOrderAttributeValue : Option (Terminated 1)  -- tag 21088

def NewWholesaleOrder.parts (record : NewWholesaleOrder) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 49, 48, 56, 51] record.wholesaleTradeType,
   Part.optional [50, 49, 48, 56, 53] record.lISTransactionID,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.required [52, 52] record.price,
   Part.required [53, 51] record.quantity,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.required [50, 49, 48, 56, 50] record.wholesaleSide,
   Part.optional [50, 49, 48, 57, 54] record.eSCBMembership,
   Part.optional [50, 49, 56, 48, 51] record.messagePriceNotation,
   Part.optional [49, 51, 57, 48] record.tradePublicationType,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSo,
   Part.required [54, 48, 57] record.legSecurityType,
   Part.optional [50, 49, 48, 57, 50] record.legLastTradingDate,
   Part.optional [49, 51, 53, 56] record.legPutOrCall,
   Part.required [53, 54, 54] record.legPrice,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [50, 49, 48, 56, 57] record.bidNonExecClID,
   Part.optional [50, 49, 48, 57, 48] record.offerNonExecClID,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.optional [50, 49, 48, 57, 49] record.legRatio,
   Part.optional [53, 53, 50] record.noSides,
   Part.required [53, 52] record.side,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [53, 56] record.text,
   Part.optional [49] record.account,
   Part.required [54, 51, 57, 57] record.accountCode,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.required [50, 57] record.lastCapacity,
   Part.optional [50, 49, 56, 48, 52] record.longClientID,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [50, 49, 48, 56, 54] record.noNestedOrderAttributes,
   Part.optional [50, 49, 48, 56, 55] record.nestedOrderAttributeType,
   Part.optional [50, 49, 48, 56, 56] record.nestedOrderAttributeValue]

def NewWholesaleOrder.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[50, 49, 48, 56, 51]], [[50, 49, 48, 56, 53]], [[49, 54, 55]], [[55, 54, 50]], [[52, 52]], [[53, 51]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 49, 48, 56, 50]], [[50, 49, 48, 57, 54]], [[50, 49, 56, 48, 51]], [[49, 51, 57, 48]], [[53, 53, 53]], [[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 48, 57]], [[50, 49, 48, 57, 50]], [[49, 51, 53, 56]], [[53, 54, 54]], [[54, 50, 52]], [[49, 51, 52]], [[49, 51, 53]], [[50, 49, 48, 56, 57]], [[50, 49, 48, 57, 48]], [[54, 49, 50]], [[50, 49, 48, 57, 49]], [[53, 53, 50]], [[53, 52]], [[53, 55, 55]], [[53, 56]], [[49]], [[54, 51, 57, 57]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[50, 57]], [[50, 49, 56, 48, 52]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[50, 49, 48, 56, 54]], [[50, 49, 48, 56, 55]], [[50, 49, 48, 56, 56]]]

theorem NewWholesaleOrder.shape (record : NewWholesaleOrder) : record.parts.map Part.tags = NewWholesaleOrder.tags := rfl

def NewWholesaleOrder.decode (tokens : List Token) : Option NewWholesaleOrder := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let wholesaleTradeType ← readRequired [50, 49, 48, 56, 51] tokens
  let lISTransactionID ← readOptional [50, 49, 48, 56, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let price ← readRequired [52, 52] tokens
  let quantity ← readRequired [53, 51] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let wholesaleSide ← readRequired [50, 49, 48, 56, 50] tokens
  let eSCBMembership ← readOptional [50, 49, 48, 57, 54] tokens
  let messagePriceNotation ← readOptional [50, 49, 56, 48, 51] tokens
  let tradePublicationType ← readOptional [49, 51, 57, 48] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readRequired [54, 48, 50] tokens
  let legSecurityIDSo ← readOptional [54, 48, 51] tokens
  let legSecurityType ← readRequired [54, 48, 57] tokens
  let legLastTradingDate ← readOptional [50, 49, 48, 57, 50] tokens
  let legPutOrCall ← readOptional [49, 51, 53, 56] tokens
  let legPrice ← readRequired [53, 54, 54] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let bidNonExecClID ← readOptional [50, 49, 48, 56, 57] tokens
  let offerNonExecClID ← readOptional [50, 49, 48, 57, 48] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatio ← readOptional [50, 49, 48, 57, 49] tokens
  let noSides ← readOptional [53, 53, 50] tokens
  let side ← readRequired [53, 52] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let account ← readOptional [49] tokens
  let accountCode ← readRequired [54, 51, 57, 57] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let lastCapacity ← readRequired [50, 57] tokens
  let longClientID ← readOptional [50, 49, 56, 48, 52] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let noNestedOrderAttributes ← readOptional [50, 49, 48, 56, 54] tokens
  let nestedOrderAttributeType ← readOptional [50, 49, 48, 56, 55] tokens
  let nestedOrderAttributeValue ← readOptional [50, 49, 48, 56, 56] tokens
  pure { clOrdID, securityID, securityIDSource, wholesaleTradeType, lISTransactionID, securityType, securitySubType, price, quantity, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, wholesaleSide, eSCBMembership, messagePriceNotation, tradePublicationType, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legSecurityType, legLastTradingDate, legPutOrCall, legPrice, legSide, bidSize, offerSize, bidNonExecClID, offerNonExecClID, legStrikePrice, legRatio, noSides, side, clearingInstructi, text, account, accountCode, technicalOrdType, postingAction, lastCapacity, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noNestedOrderAttributes, nestedOrderAttributeType, nestedOrderAttributeValue }

theorem NewWholesaleOrder.decode_agrees (record : NewWholesaleOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ NewWholesaleOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewWholesaleOrder.decode tokens = some record := by
  have distinct : NewWholesaleOrder.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have wholesaleTradeType := readRequired_part [50, 49, 48, 56, 51] record.wholesaleTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lISTransactionID := readOptional_part [50, 49, 48, 56, 53] record.lISTransactionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have quantity := readRequired_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have wholesaleSide := readRequired_part [50, 49, 48, 56, 50] record.wholesaleSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have eSCBMembership := readOptional_part [50, 49, 48, 57, 54] record.eSCBMembership tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have messagePriceNotation := readOptional_part [50, 49, 56, 48, 51] record.messagePriceNotation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tradePublicationType := readOptional_part [49, 51, 57, 48] record.tradePublicationType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have legSecurityID := readRequired_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have legSecurityIDSo := readOptional_part [54, 48, 51] record.legSecurityIDSo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have legSecurityType := readRequired_part [54, 48, 57] record.legSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have legLastTradingDate := readOptional_part [50, 49, 48, 57, 50] record.legLastTradingDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have legPutOrCall := readOptional_part [49, 51, 53, 56] record.legPutOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have legPrice := readRequired_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have bidNonExecClID := readOptional_part [50, 49, 48, 56, 57] record.bidNonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have offerNonExecClID := readOptional_part [50, 49, 48, 57, 48] record.offerNonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have legRatio := readOptional_part [50, 49, 48, 57, 49] record.legRatio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have noSides := readOptional_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have accountCode := readRequired_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have lastCapacity := readRequired_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have longClientID := readOptional_part [50, 49, 56, 48, 52] record.longClientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have noNestedOrderAttributes := readOptional_part [50, 49, 48, 56, 54] record.noNestedOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have nestedOrderAttributeType := readOptional_part [50, 49, 48, 56, 55] record.nestedOrderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have nestedOrderAttributeValue := readOptional_part [50, 49, 48, 56, 56] record.nestedOrderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  simp only [NewWholesaleOrder.decode, clOrdID, securityID, securityIDSource, wholesaleTradeType, lISTransactionID, securityType, securitySubType, price, quantity, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, wholesaleSide, eSCBMembership, messagePriceNotation, tradePublicationType, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legSecurityType, legLastTradingDate, legPutOrCall, legPrice, legSide, bidSize, offerSize, bidNonExecClID, offerNonExecClID, legStrikePrice, legRatio, noSides, side, clearingInstructi, text, account, accountCode, technicalOrdType, postingAction, lastCapacity, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noNestedOrderAttributes, nestedOrderAttributeType, nestedOrderAttributeValue, some_bind] <;> rfl

structure RequestForImpliedExecution where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  orderID : Terminated 1  -- tag 37
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384

def RequestForImpliedExecution.parts (record : RequestForImpliedExecution) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [51, 55] record.orderID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier]

def RequestForImpliedExecution.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]]]

theorem RequestForImpliedExecution.shape (record : RequestForImpliedExecution) : record.parts.map Part.tags = RequestForImpliedExecution.tags := rfl

def RequestForImpliedExecution.decode (tokens : List Token) : Option RequestForImpliedExecution := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  pure { clOrdID, securityID, securityIDSource, eMM, orderID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier }

theorem RequestForImpliedExecution.decode_agrees (record : RequestForImpliedExecution) (tokens : List Token)
    (agrees : ∀ tags ∈ RequestForImpliedExecution.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RequestForImpliedExecution.decode tokens = some record := by
  have distinct : RequestForImpliedExecution.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [RequestForImpliedExecution.decode, clOrdID, securityID, securityIDSource, eMM, orderID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, some_bind] <;> rfl

structure CrossOrder where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  price : Terminated 1  -- tag 44
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  nonExecClID : Option (Terminated 1)  -- tag 21081
  orderActorType : Terminated 1  -- tag 21109
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  messagePriceNotation : Option (Terminated 1)  -- tag 21803
  side : Terminated 1  -- tag 54
  clearingInstructi : Option (Terminated 1)  -- tag 577
  text : Option (Terminated 1)  -- tag 58
  account : Option (Terminated 1)  -- tag 1
  accountCode : Terminated 1  -- tag 6399
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  lastCapacity : Terminated 1  -- tag 29
  longClientID : Option (Terminated 1)  -- tag 21804
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  noLegs : Option (Terminated 1)  -- tag 555
  legSymbol : Option (Terminated 1)  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSo : Option (Terminated 1)  -- tag 603
  legLastPx : Option (Terminated 1)  -- tag 637
  legLastQty : Option (Terminated 1)  -- tag 1418
  orderTolerablePrice : Option (Terminated 1)  -- tag 21822

def CrossOrder.parts (record : CrossOrder) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [50, 49, 48, 56, 49] record.nonExecClID,
   Part.required [50, 49, 49, 48, 57] record.orderActorType,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [50, 49, 56, 48, 51] record.messagePriceNotation,
   Part.required [53, 52] record.side,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [53, 56] record.text,
   Part.optional [49] record.account,
   Part.required [54, 51, 57, 57] record.accountCode,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.required [50, 57] record.lastCapacity,
   Part.optional [50, 49, 56, 48, 52] record.longClientID,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [53, 53, 53] record.noLegs,
   Part.optional [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSo,
   Part.optional [54, 51, 55] record.legLastPx,
   Part.optional [49, 52, 49, 56] record.legLastQty,
   Part.optional [50, 49, 56, 50, 50] record.orderTolerablePrice]

def CrossOrder.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[52, 52]], [[51, 56]], [[52, 48]], [[50, 49, 48, 56, 49]], [[50, 49, 49, 48, 57]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 49, 56, 48, 51]], [[53, 52]], [[53, 55, 55]], [[53, 56]], [[49]], [[54, 51, 57, 57]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[50, 57]], [[50, 49, 56, 48, 52]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[53, 53, 53]], [[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 51, 55]], [[49, 52, 49, 56]], [[50, 49, 56, 50, 50]]]

theorem CrossOrder.shape (record : CrossOrder) : record.parts.map Part.tags = CrossOrder.tags := rfl

def CrossOrder.decode (tokens : List Token) : Option CrossOrder := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let price ← readRequired [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let nonExecClID ← readOptional [50, 49, 48, 56, 49] tokens
  let orderActorType ← readRequired [50, 49, 49, 48, 57] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let messagePriceNotation ← readOptional [50, 49, 56, 48, 51] tokens
  let side ← readRequired [53, 52] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let text ← readOptional [53, 56] tokens
  let account ← readOptional [49] tokens
  let accountCode ← readRequired [54, 51, 57, 57] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let lastCapacity ← readRequired [50, 57] tokens
  let longClientID ← readOptional [50, 49, 56, 48, 52] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let noLegs ← readOptional [53, 53, 53] tokens
  let legSymbol ← readOptional [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSo ← readOptional [54, 48, 51] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  let legLastQty ← readOptional [49, 52, 49, 56] tokens
  let orderTolerablePrice ← readOptional [50, 49, 56, 50, 50] tokens
  pure { clOrdID, securityID, securityIDSource, eMM, price, orderQty, ordType, nonExecClID, orderActorType, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, messagePriceNotation, side, clearingInstructi, text, account, accountCode, technicalOrdType, postingAction, lastCapacity, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legLastPx, legLastQty, orderTolerablePrice }

theorem CrossOrder.decode_agrees (record : CrossOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ CrossOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CrossOrder.decode tokens = some record := by
  have distinct : CrossOrder.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have nonExecClID := readOptional_part [50, 49, 48, 56, 49] record.nonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderActorType := readRequired_part [50, 49, 49, 48, 57] record.orderActorType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have messagePriceNotation := readOptional_part [50, 49, 56, 48, 51] record.messagePriceNotation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have accountCode := readRequired_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have lastCapacity := readRequired_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have longClientID := readOptional_part [50, 49, 56, 48, 52] record.longClientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have noLegs := readOptional_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have legSymbol := readOptional_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have legSecurityID := readOptional_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have legSecurityIDSo := readOptional_part [54, 48, 51] record.legSecurityIDSo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have legLastPx := readOptional_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have legLastQty := readOptional_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have orderTolerablePrice := readOptional_part [50, 49, 56, 50, 50] record.orderTolerablePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  simp only [CrossOrder.decode, clOrdID, securityID, securityIDSource, eMM, price, orderQty, ordType, nonExecClID, orderActorType, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, messagePriceNotation, side, clearingInstructi, text, account, accountCode, technicalOrdType, postingAction, lastCapacity, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legLastPx, legLastQty, orderTolerablePrice, some_bind] <;> rfl

structure ERGCommand where
  requestID : Terminated 1  -- tag 21060
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  eRGActionType : Terminated 1  -- tag 21097
  targetFirmID : Terminated 1  -- tag 21098
  targetPartyID : Option (Terminated 1)  -- tag 21095
  targetClientShortCode : Option (Terminated 1)  -- tag 21108
  targetLogicalAccessID : Option (Terminated 1)  -- tag 21099
  purge : Option (Terminated 1)  -- tag 21100
  oSLFlag : Option (Terminated 1)  -- tag 21101
  orderSizeLimit : Option (Terminated 1)  -- tag 21102
  oALFlag : Option (Terminated 1)  -- tag 21808
  orderAmountLimit : Option (Terminated 1)  -- tag 21809
  mEPFlag : Option (Terminated 1)  -- tag 21811
  maximumLongExposure : Option (Terminated 1)  -- tag 21812
  maximumShortExposure : Option (Terminated 1)  -- tag 21813
  mEPBreachAction : Option (Terminated 1)  -- tag 21814
  noThresholds : Option (Terminated 1)  -- tag 21815
  thresholdValue : Option (Terminated 1)  -- tag 21817
  thresholdBreachAction : Option (Terminated 1)  -- tag 21816
  marketCondition : Option (Terminated 1)  -- tag 21823

def ERGCommand.parts (record : ERGCommand) : List Part :=
  [Part.required [50, 49, 48, 54, 48] record.requestID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.required [50, 49, 48, 57, 55] record.eRGActionType,
   Part.required [50, 49, 48, 57, 56] record.targetFirmID,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.optional [50, 49, 49, 48, 56] record.targetClientShortCode,
   Part.optional [50, 49, 48, 57, 57] record.targetLogicalAccessID,
   Part.optional [50, 49, 49, 48, 48] record.purge,
   Part.optional [50, 49, 49, 48, 49] record.oSLFlag,
   Part.optional [50, 49, 49, 48, 50] record.orderSizeLimit,
   Part.optional [50, 49, 56, 48, 56] record.oALFlag,
   Part.optional [50, 49, 56, 48, 57] record.orderAmountLimit,
   Part.optional [50, 49, 56, 49, 49] record.mEPFlag,
   Part.optional [50, 49, 56, 49, 50] record.maximumLongExposure,
   Part.optional [50, 49, 56, 49, 51] record.maximumShortExposure,
   Part.optional [50, 49, 56, 49, 52] record.mEPBreachAction,
   Part.optional [50, 49, 56, 49, 53] record.noThresholds,
   Part.optional [50, 49, 56, 49, 55] record.thresholdValue,
   Part.optional [50, 49, 56, 49, 54] record.thresholdBreachAction,
   Part.optional [50, 49, 56, 50, 51] record.marketCondition]

def ERGCommand.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 54, 48]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[50, 49, 48, 57, 55]], [[50, 49, 48, 57, 56]], [[50, 49, 48, 57, 53]], [[50, 49, 49, 48, 56]], [[50, 49, 48, 57, 57]], [[50, 49, 49, 48, 48]], [[50, 49, 49, 48, 49]], [[50, 49, 49, 48, 50]], [[50, 49, 56, 48, 56]], [[50, 49, 56, 48, 57]], [[50, 49, 56, 49, 49]], [[50, 49, 56, 49, 50]], [[50, 49, 56, 49, 51]], [[50, 49, 56, 49, 52]], [[50, 49, 56, 49, 53]], [[50, 49, 56, 49, 55]], [[50, 49, 56, 49, 54]], [[50, 49, 56, 50, 51]]]

theorem ERGCommand.shape (record : ERGCommand) : record.parts.map Part.tags = ERGCommand.tags := rfl

def ERGCommand.decode (tokens : List Token) : Option ERGCommand := do
  let requestID ← readRequired [50, 49, 48, 54, 48] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let eRGActionType ← readRequired [50, 49, 48, 57, 55] tokens
  let targetFirmID ← readRequired [50, 49, 48, 57, 56] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let targetClientShortCode ← readOptional [50, 49, 49, 48, 56] tokens
  let targetLogicalAccessID ← readOptional [50, 49, 48, 57, 57] tokens
  let purge ← readOptional [50, 49, 49, 48, 48] tokens
  let oSLFlag ← readOptional [50, 49, 49, 48, 49] tokens
  let orderSizeLimit ← readOptional [50, 49, 49, 48, 50] tokens
  let oALFlag ← readOptional [50, 49, 56, 48, 56] tokens
  let orderAmountLimit ← readOptional [50, 49, 56, 48, 57] tokens
  let mEPFlag ← readOptional [50, 49, 56, 49, 49] tokens
  let maximumLongExposure ← readOptional [50, 49, 56, 49, 50] tokens
  let maximumShortExposure ← readOptional [50, 49, 56, 49, 51] tokens
  let mEPBreachAction ← readOptional [50, 49, 56, 49, 52] tokens
  let noThresholds ← readOptional [50, 49, 56, 49, 53] tokens
  let thresholdValue ← readOptional [50, 49, 56, 49, 55] tokens
  let thresholdBreachAction ← readOptional [50, 49, 56, 49, 54] tokens
  let marketCondition ← readOptional [50, 49, 56, 50, 51] tokens
  pure { requestID, securityID, securityIDSource, eMM, eRGActionType, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, purge, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, noThresholds, thresholdValue, thresholdBreachAction, marketCondition }

theorem ERGCommand.decode_agrees (record : ERGCommand) (tokens : List Token)
    (agrees : ∀ tags ∈ ERGCommand.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ERGCommand.decode tokens = some record := by
  have distinct : ERGCommand.tags.flatten.Nodup := by decide +kernel
  have requestID := readRequired_part [50, 49, 48, 54, 48] record.requestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have eRGActionType := readRequired_part [50, 49, 48, 57, 55] record.eRGActionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetFirmID := readRequired_part [50, 49, 48, 57, 56] record.targetFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetClientShortCode := readOptional_part [50, 49, 49, 48, 56] record.targetClientShortCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have targetLogicalAccessID := readOptional_part [50, 49, 48, 57, 57] record.targetLogicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have purge := readOptional_part [50, 49, 49, 48, 48] record.purge tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have oSLFlag := readOptional_part [50, 49, 49, 48, 49] record.oSLFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderSizeLimit := readOptional_part [50, 49, 49, 48, 50] record.orderSizeLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have oALFlag := readOptional_part [50, 49, 56, 48, 56] record.oALFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderAmountLimit := readOptional_part [50, 49, 56, 48, 57] record.orderAmountLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have mEPFlag := readOptional_part [50, 49, 56, 49, 49] record.mEPFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maximumLongExposure := readOptional_part [50, 49, 56, 49, 50] record.maximumLongExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maximumShortExposure := readOptional_part [50, 49, 56, 49, 51] record.maximumShortExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have mEPBreachAction := readOptional_part [50, 49, 56, 49, 52] record.mEPBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noThresholds := readOptional_part [50, 49, 56, 49, 53] record.noThresholds tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have thresholdValue := readOptional_part [50, 49, 56, 49, 55] record.thresholdValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have thresholdBreachAction := readOptional_part [50, 49, 56, 49, 54] record.thresholdBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have marketCondition := readOptional_part [50, 49, 56, 50, 51] record.marketCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [ERGCommand.decode, requestID, securityID, securityIDSource, eMM, eRGActionType, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, purge, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, noThresholds, thresholdValue, thresholdBreachAction, marketCondition, some_bind] <;> rfl

structure GetRiskControls where
  requestID : Terminated 1  -- tag 21060
  targetFirmID : Terminated 1  -- tag 21098
  targetPartyID : Option (Terminated 1)  -- tag 21095
  targetClientShortCode : Option (Terminated 1)  -- tag 21108
  targetLogicalAccessID : Option (Terminated 1)  -- tag 21099
  riskControlType : Terminated 1  -- tag 21103
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def GetRiskControls.parts (record : GetRiskControls) : List Part :=
  [Part.required [50, 49, 48, 54, 48] record.requestID,
   Part.required [50, 49, 48, 57, 56] record.targetFirmID,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.optional [50, 49, 49, 48, 56] record.targetClientShortCode,
   Part.optional [50, 49, 48, 57, 57] record.targetLogicalAccessID,
   Part.required [50, 49, 49, 48, 51] record.riskControlType,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def GetRiskControls.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 54, 48]], [[50, 49, 48, 57, 56]], [[50, 49, 48, 57, 53]], [[50, 49, 49, 48, 56]], [[50, 49, 48, 57, 57]], [[50, 49, 49, 48, 51]], [[52, 56]], [[50, 50]]]

theorem GetRiskControls.shape (record : GetRiskControls) : record.parts.map Part.tags = GetRiskControls.tags := rfl

def GetRiskControls.decode (tokens : List Token) : Option GetRiskControls := do
  let requestID ← readRequired [50, 49, 48, 54, 48] tokens
  let targetFirmID ← readRequired [50, 49, 48, 57, 56] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let targetClientShortCode ← readOptional [50, 49, 49, 48, 56] tokens
  let targetLogicalAccessID ← readOptional [50, 49, 48, 57, 57] tokens
  let riskControlType ← readRequired [50, 49, 49, 48, 51] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { requestID, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, riskControlType, securityID, securityIDSource }

theorem GetRiskControls.decode_agrees (record : GetRiskControls) (tokens : List Token)
    (agrees : ∀ tags ∈ GetRiskControls.tags, select tags tokens = select tags (encodeParts record.parts)) :
    GetRiskControls.decode tokens = some record := by
  have distinct : GetRiskControls.tags.flatten.Nodup := by decide +kernel
  have requestID := readRequired_part [50, 49, 48, 54, 48] record.requestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetFirmID := readRequired_part [50, 49, 48, 57, 56] record.targetFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetClientShortCode := readOptional_part [50, 49, 49, 48, 56] record.targetClientShortCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetLogicalAccessID := readOptional_part [50, 49, 48, 57, 57] record.targetLogicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have riskControlType := readRequired_part [50, 49, 49, 48, 51] record.riskControlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [GetRiskControls.decode, requestID, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, riskControlType, securityID, securityIDSource, some_bind] <;> rfl

structure IOI where
  iOIID : Terminated 1  -- tag 23
  iOITransType : Terminated 1  -- tag 28
  iOIRefID : Option (Terminated 1)  -- tag 26
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  side : Terminated 1  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  iOIQty : Terminated 1  -- tag 27
  iOIQltyInd : Option (Terminated 1)  -- tag 25
  noRoutingIDS : Terminated 1  -- tag 215
  routingTypes : Terminated 1  -- tag 216
  routingID : Terminated 1  -- tag 217

def IOI.parts (record : IOI) : List Part :=
  [Part.required [50, 51] record.iOIID,
   Part.required [50, 56] record.iOITransType,
   Part.optional [50, 54] record.iOIRefID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.required [50, 55] record.iOIQty,
   Part.optional [50, 53] record.iOIQltyInd,
   Part.required [50, 49, 53] record.noRoutingIDS,
   Part.required [50, 49, 54] record.routingTypes,
   Part.required [50, 49, 55] record.routingID]

def IOI.tags : List (List (List UInt8)) :=
  [[[50, 51]], [[50, 56]], [[50, 54]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[53, 52]], [[51, 56]], [[50, 55]], [[50, 53]], [[50, 49, 53]], [[50, 49, 54]], [[50, 49, 55]]]

theorem IOI.shape (record : IOI) : record.parts.map Part.tags = IOI.tags := rfl

def IOI.decode (tokens : List Token) : Option IOI := do
  let iOIID ← readRequired [50, 51] tokens
  let iOITransType ← readRequired [50, 56] tokens
  let iOIRefID ← readOptional [50, 54] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let iOIQty ← readRequired [50, 55] tokens
  let iOIQltyInd ← readOptional [50, 53] tokens
  let noRoutingIDS ← readRequired [50, 49, 53] tokens
  let routingTypes ← readRequired [50, 49, 54] tokens
  let routingID ← readRequired [50, 49, 55] tokens
  pure { iOIID, iOITransType, iOIRefID, securityID, securityIDSource, eMM, side, orderQty, iOIQty, iOIQltyInd, noRoutingIDS, routingTypes, routingID }

theorem IOI.decode_agrees (record : IOI) (tokens : List Token)
    (agrees : ∀ tags ∈ IOI.tags, select tags tokens = select tags (encodeParts record.parts)) :
    IOI.decode tokens = some record := by
  have distinct : IOI.tags.flatten.Nodup := by decide +kernel
  have iOIID := readRequired_part [50, 51] record.iOIID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have iOITransType := readRequired_part [50, 56] record.iOITransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have iOIRefID := readOptional_part [50, 54] record.iOIRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have iOIQty := readRequired_part [50, 55] record.iOIQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have iOIQltyInd := readOptional_part [50, 53] record.iOIQltyInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noRoutingIDS := readRequired_part [50, 49, 53] record.noRoutingIDS tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have routingTypes := readRequired_part [50, 49, 54] record.routingTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have routingID := readRequired_part [50, 49, 55] record.routingID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [IOI.decode, iOIID, iOITransType, iOIRefID, securityID, securityIDSource, eMM, side, orderQty, iOIQty, iOIQltyInd, noRoutingIDS, routingTypes, routingID, some_bind] <;> rfl

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeReportTransType : Terminated 1  -- tag 487
  tradeReportType : Option (Terminated 1)  -- tag 856
  trdType : Option (Terminated 1)  -- tag 828
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  noRegulatoryTradeIDs : Option (Terminated 1)  -- tag 1907
  regulatoryTradeID : Option (Terminated 1)  -- tag 1903
  regulatoryTradeIDType : Option (Terminated 1)  -- tag 1906
  noSides : Option (Terminated 1)  -- tag 552
  side : Option (Terminated 1)  -- tag 54
  account : Option (Terminated 1)  -- tag 1
  accountCode : Option (Terminated 1)  -- tag 6399
  lastCapacity : Option (Terminated 1)  -- tag 29
  text : Option (Terminated 1)  -- tag 58
  principalCode : Option (Terminated 1)  -- tag 20155
  quantity : Option (Terminated 1)  -- tag 53
  price : Option (Terminated 1)  -- tag 44
  noPartyIDs : Option (Terminated 1)  -- tag 453
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  partyRoleQualifi : Option (Terminated 1)  -- tag 2376
  mICofSecondaryListing : Option (Terminated 1)  -- tag 21065
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  orderOrigination : Option (Terminated 1)  -- tag 1724
  deferralIndicator : Option (Terminated 1)  -- tag 21063
  settlPeriod : Option (Terminated 1)  -- tag 10055
  settlementFlag : Option (Terminated 1)  -- tag 9970
  guaranteeFlag : Option (Terminated 1)  -- tag 9971
  vWAPBegTime : Option (Terminated 1)  -- tag 10026
  vWAPEndTime : Option (Terminated 1)  -- tag 10027
  grossTradeAmt : Option (Terminated 1)  -- tag 381
  centralisationDate : Option (Terminated 1)  -- tag 21068

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [56, 50, 56] record.trdType,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [49, 57, 48, 55] record.noRegulatoryTradeIDs,
   Part.optional [49, 57, 48, 51] record.regulatoryTradeID,
   Part.optional [49, 57, 48, 54] record.regulatoryTradeIDType,
   Part.optional [53, 53, 50] record.noSides,
   Part.optional [53, 52] record.side,
   Part.optional [49] record.account,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 49, 53, 53] record.principalCode,
   Part.optional [53, 51] record.quantity,
   Part.optional [52, 52] record.price,
   Part.optional [52, 53, 51] record.noPartyIDs,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 49, 48, 54, 53] record.mICofSecondaryListing,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 49, 48, 54, 51] record.deferralIndicator,
   Part.optional [49, 48, 48, 53, 53] record.settlPeriod,
   Part.optional [57, 57, 55, 48] record.settlementFlag,
   Part.optional [57, 57, 55, 49] record.guaranteeFlag,
   Part.optional [49, 48, 48, 50, 54] record.vWAPBegTime,
   Part.optional [49, 48, 48, 50, 55] record.vWAPEndTime,
   Part.optional [51, 56, 49] record.grossTradeAmt,
   Part.optional [50, 49, 48, 54, 56] record.centralisationDate]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[49, 48, 48, 51]], [[52, 56, 55]], [[56, 53, 54]], [[56, 50, 56]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[49, 57, 48, 55]], [[49, 57, 48, 51]], [[49, 57, 48, 54]], [[53, 53, 50]], [[53, 52]], [[49]], [[54, 51, 57, 57]], [[50, 57]], [[53, 56]], [[50, 48, 49, 53, 53]], [[53, 51]], [[52, 52]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 49, 48, 54, 53]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[49, 55, 50, 52]], [[50, 49, 48, 54, 51]], [[49, 48, 48, 53, 53]], [[57, 57, 55, 48]], [[57, 57, 55, 49]], [[49, 48, 48, 50, 54]], [[49, 48, 48, 50, 55]], [[51, 56, 49]], [[50, 49, 48, 54, 56]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let noRegulatoryTradeIDs ← readOptional [49, 57, 48, 55] tokens
  let regulatoryTradeID ← readOptional [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readOptional [49, 57, 48, 54] tokens
  let noSides ← readOptional [53, 53, 50] tokens
  let side ← readOptional [53, 52] tokens
  let account ← readOptional [49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let text ← readOptional [53, 56] tokens
  let principalCode ← readOptional [50, 48, 49, 53, 53] tokens
  let quantity ← readOptional [53, 51] tokens
  let price ← readOptional [52, 52] tokens
  let noPartyIDs ← readOptional [52, 53, 51] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let partyRoleQualifi ← readOptional [50, 51, 55, 54] tokens
  let mICofSecondaryListing ← readOptional [50, 49, 48, 54, 53] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let deferralIndicator ← readOptional [50, 49, 48, 54, 51] tokens
  let settlPeriod ← readOptional [49, 48, 48, 53, 53] tokens
  let settlementFlag ← readOptional [57, 57, 55, 48] tokens
  let guaranteeFlag ← readOptional [57, 57, 55, 49] tokens
  let vWAPBegTime ← readOptional [49, 48, 48, 50, 54] tokens
  let vWAPEndTime ← readOptional [49, 48, 48, 50, 55] tokens
  let grossTradeAmt ← readOptional [51, 56, 49] tokens
  let centralisationDate ← readOptional [50, 49, 48, 54, 56] tokens
  pure { tradeReportID, tradeID, tradeReportTransType, tradeReportType, trdType, securityID, securityIDSource, eMM, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, noSides, side, account, accountCode, lastCapacity, text, principalCode, quantity, price, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, mICofSecondaryListing, noOrderAttribut, orderAttributeTy, orderAttributeValue, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, orderOrigination, deferralIndicator, settlPeriod, settlementFlag, guaranteeFlag, vWAPBegTime, vWAPEndTime, grossTradeAmt, centralisationDate }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noRegulatoryTradeIDs := readOptional_part [49, 57, 48, 55] record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have regulatoryTradeID := readOptional_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have regulatoryTradeIDType := readOptional_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noSides := readOptional_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have principalCode := readOptional_part [50, 48, 49, 53, 53] record.principalCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have quantity := readOptional_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have partyRoleQualifi := readOptional_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have mICofSecondaryListing := readOptional_part [50, 49, 48, 54, 53] record.mICofSecondaryListing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have deferralIndicator := readOptional_part [50, 49, 48, 54, 51] record.deferralIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have settlPeriod := readOptional_part [49, 48, 48, 53, 53] record.settlPeriod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have settlementFlag := readOptional_part [57, 57, 55, 48] record.settlementFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have guaranteeFlag := readOptional_part [57, 57, 55, 49] record.guaranteeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have vWAPBegTime := readOptional_part [49, 48, 48, 50, 54] record.vWAPBegTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have vWAPEndTime := readOptional_part [49, 48, 48, 50, 55] record.vWAPEndTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have grossTradeAmt := readOptional_part [51, 56, 49] record.grossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have centralisationDate := readOptional_part [50, 49, 48, 54, 56] record.centralisationDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, tradeID, tradeReportTransType, tradeReportType, trdType, securityID, securityIDSource, eMM, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, noSides, side, account, accountCode, lastCapacity, text, principalCode, quantity, price, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, mICofSecondaryListing, noOrderAttribut, orderAttributeTy, orderAttributeValue, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, orderOrigination, deferralIndicator, settlPeriod, settlementFlag, guaranteeFlag, vWAPBegTime, vWAPEndTime, grossTradeAmt, centralisationDate, some_bind] <;> rfl

structure FundPriceInput where
  clOrdID : Terminated 1  -- tag 11
  securityIDSource : Terminated 1  -- tag 22
  securityID : Terminated 1  -- tag 48
  eMM : Terminated 1  -- tag 20020
  price : Terminated 1  -- tag 44
  byPassControlFlag : Option (Terminated 1)  -- tag 10053

def FundPriceInput.parts (record : FundPriceInput) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [52, 56] record.securityID,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [52, 52] record.price,
   Part.optional [49, 48, 48, 53, 51] record.byPassControlFlag]

def FundPriceInput.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[50, 50]], [[52, 56]], [[50, 48, 48, 50, 48]], [[52, 52]], [[49, 48, 48, 53, 51]]]

theorem FundPriceInput.shape (record : FundPriceInput) : record.parts.map Part.tags = FundPriceInput.tags := rfl

def FundPriceInput.decode (tokens : List Token) : Option FundPriceInput := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let securityID ← readRequired [52, 56] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let price ← readRequired [52, 52] tokens
  let byPassControlFlag ← readOptional [49, 48, 48, 53, 51] tokens
  pure { clOrdID, securityIDSource, securityID, eMM, price, byPassControlFlag }

theorem FundPriceInput.decode_agrees (record : FundPriceInput) (tokens : List Token)
    (agrees : ∀ tags ∈ FundPriceInput.tags, select tags tokens = select tags (encodeParts record.parts)) :
    FundPriceInput.decode tokens = some record := by
  have distinct : FundPriceInput.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have byPassControlFlag := readOptional_part [49, 48, 48, 53, 51] record.byPassControlFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [FundPriceInput.decode, clOrdID, securityIDSource, securityID, eMM, price, byPassControlFlag, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | massQuote (header : Header) (r0 : MassQuote)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | ownershipRequest (header : Header) (r0 : OwnershipRequest)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | priceInput (header : Header) (r0 : PriceInput)
  | liquidityProviderCommand (header : Header) (r0 : LiquidityProviderCommand)
  | orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | newWholesaleOrder (header : Header) (r0 : NewWholesaleOrder)
  | requestForImpliedExecution (header : Header) (r0 : RequestForImpliedExecution)
  | crossOrder (header : Header) (r0 : CrossOrder)
  | eRGCommand (header : Header) (r0 : ERGCommand)
  | getRiskControls (header : Header) (r0 : GetRiskControls)
  | iOI (header : Header) (r0 : IOI)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | fundPriceInput (header : Header) (r0 : FundPriceInput)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuote header r0 => ⟨[51, 53], ⟨[105], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .ownershipRequest header r0 => ⟨[51, 53], ⟨[85, 49, 56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .priceInput header r0 => ⟨[51, 53], ⟨[85, 73], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .liquidityProviderCommand header r0 => ⟨[51, 53], ⟨[85, 90], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassStatusRequest header r0 => ⟨[51, 53], ⟨[65, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], ⟨[113], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newWholesaleOrder header r0 => ⟨[51, 53], ⟨[85, 54, 52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .requestForImpliedExecution header r0 => ⟨[51, 53], ⟨[85, 54, 54], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .crossOrder header r0 => ⟨[51, 53], ⟨[85, 54, 55], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eRGCommand header r0 => ⟨[51, 53], ⟨[85, 54, 56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .getRiskControls header r0 => ⟨[51, 53], ⟨[85, 55, 48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .iOI header r0 => ⟨[51, 53], ⟨[54], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .fundPriceInput header r0 => ⟨[51, 53], ⟨[85, 52, 52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
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
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [105] then
        if known (Header.tags ++ MassQuote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuote.decode rest
          pure (.massQuote header r0)
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
      else if token.value.val = [85, 49, 56] then
        if known (Header.tags ++ OwnershipRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OwnershipRequest.decode rest
          pure (.ownershipRequest header r0)
        else none
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value.val = [85, 73] then
        if known (Header.tags ++ PriceInput.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PriceInput.decode rest
          pure (.priceInput header r0)
        else none
      else if token.value.val = [85, 90] then
        if known (Header.tags ++ LiquidityProviderCommand.tags) rest then do
          let header ← Header.decode rest
          let r0 ← LiquidityProviderCommand.decode rest
          pure (.liquidityProviderCommand header r0)
        else none
      else if token.value.val = [65, 70] then
        if known (Header.tags ++ OrderMassStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassStatusRequest.decode rest
          pure (.orderMassStatusRequest header r0)
        else none
      else if token.value.val = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
        else none
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value.val = [85, 54, 52] then
        if known (Header.tags ++ NewWholesaleOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewWholesaleOrder.decode rest
          pure (.newWholesaleOrder header r0)
        else none
      else if token.value.val = [85, 54, 54] then
        if known (Header.tags ++ RequestForImpliedExecution.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RequestForImpliedExecution.decode rest
          pure (.requestForImpliedExecution header r0)
        else none
      else if token.value.val = [85, 54, 55] then
        if known (Header.tags ++ CrossOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CrossOrder.decode rest
          pure (.crossOrder header r0)
        else none
      else if token.value.val = [85, 54, 56] then
        if known (Header.tags ++ ERGCommand.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ERGCommand.decode rest
          pure (.eRGCommand header r0)
        else none
      else if token.value.val = [85, 55, 48] then
        if known (Header.tags ++ GetRiskControls.tags) rest then do
          let header ← Header.decode rest
          let r0 ← GetRiskControls.decode rest
          pure (.getRiskControls header r0)
        else none
      else if token.value.val = [54] then
        if known (Header.tags ++ IOI.tags) rest then do
          let header ← Header.decode rest
          let r0 ← IOI.decode rest
          pure (.iOI header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [85, 52, 52] then
        if known (Header.tags ++ FundPriceInput.tags) rest then do
          let header ← Header.decode rest
          let r0 ← FundPriceInput.decode rest
          pure (.fundPriceInput header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuote (header : Header) (r0 : MassQuote) :
    Message.decode (Message.tokens (.massQuote header r0)) = some (.massQuote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuote.tags) rfl
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

theorem Message.decode_ownershipRequest (header : Header) (r0 : OwnershipRequest) :
    Message.decode (Message.tokens (.ownershipRequest header r0)) = some (.ownershipRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OwnershipRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OwnershipRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OwnershipRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OwnershipRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_priceInput (header : Header) (r0 : PriceInput) :
    Message.decode (Message.tokens (.priceInput header r0)) = some (.priceInput header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PriceInput.tags) rfl rfl (by decide +kernel))
  have c1 := PriceInput.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PriceInput.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PriceInput.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_liquidityProviderCommand (header : Header) (r0 : LiquidityProviderCommand) :
    Message.decode (Message.tokens (.liquidityProviderCommand header r0)) = some (.liquidityProviderCommand header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (LiquidityProviderCommand.tags) rfl rfl (by decide +kernel))
  have c1 := LiquidityProviderCommand.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (LiquidityProviderCommand.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ LiquidityProviderCommand.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decode (Message.tokens (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newWholesaleOrder (header : Header) (r0 : NewWholesaleOrder) :
    Message.decode (Message.tokens (.newWholesaleOrder header r0)) = some (.newWholesaleOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewWholesaleOrder.tags) rfl rfl (by decide +kernel))
  have c1 := NewWholesaleOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewWholesaleOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewWholesaleOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_requestForImpliedExecution (header : Header) (r0 : RequestForImpliedExecution) :
    Message.decode (Message.tokens (.requestForImpliedExecution header r0)) = some (.requestForImpliedExecution header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RequestForImpliedExecution.tags) rfl rfl (by decide +kernel))
  have c1 := RequestForImpliedExecution.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RequestForImpliedExecution.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RequestForImpliedExecution.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_crossOrder (header : Header) (r0 : CrossOrder) :
    Message.decode (Message.tokens (.crossOrder header r0)) = some (.crossOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CrossOrder.tags) rfl rfl (by decide +kernel))
  have c1 := CrossOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CrossOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CrossOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_eRGCommand (header : Header) (r0 : ERGCommand) :
    Message.decode (Message.tokens (.eRGCommand header r0)) = some (.eRGCommand header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ERGCommand.tags) rfl rfl (by decide +kernel))
  have c1 := ERGCommand.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ERGCommand.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ERGCommand.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_getRiskControls (header : Header) (r0 : GetRiskControls) :
    Message.decode (Message.tokens (.getRiskControls header r0)) = some (.getRiskControls header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (GetRiskControls.tags) rfl rfl (by decide +kernel))
  have c1 := GetRiskControls.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (GetRiskControls.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ GetRiskControls.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_iOI (header : Header) (r0 : IOI) :
    Message.decode (Message.tokens (.iOI header r0)) = some (.iOI header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (IOI.tags) rfl rfl (by decide +kernel))
  have c1 := IOI.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (IOI.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ IOI.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_fundPriceInput (header : Header) (r0 : FundPriceInput) :
    Message.decode (Message.tokens (.fundPriceInput header r0)) = some (.fundPriceInput header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (FundPriceInput.tags) rfl rfl (by decide +kernel))
  have c1 := FundPriceInput.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (FundPriceInput.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ FundPriceInput.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | massQuote header r0 => exact Message.decode_massQuote header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | ownershipRequest header r0 => exact Message.decode_ownershipRequest header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | priceInput header r0 => exact Message.decode_priceInput header r0
  | liquidityProviderCommand header r0 => exact Message.decode_liquidityProviderCommand header r0
  | orderMassStatusRequest header r0 => exact Message.decode_orderMassStatusRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | newWholesaleOrder header r0 => exact Message.decode_newWholesaleOrder header r0
  | requestForImpliedExecution header r0 => exact Message.decode_requestForImpliedExecution header r0
  | crossOrder header r0 => exact Message.decode_crossOrder header r0
  | eRGCommand header r0 => exact Message.decode_eRGCommand header r0
  | getRiskControls header r0 => exact Message.decode_getRiskControls header r0
  | iOI header r0 => exact Message.decode_iOI header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | fundPriceInput header r0 => exact Message.decode_fundPriceInput header r0

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

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_massQuote (header : Header) (r0 : MassQuote) :
    Message.decodeBytes (Message.encode (.massQuote header r0)) = some (.massQuote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[105], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MassQuote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuote header r0

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

theorem Message.decodeBytes_ownershipRequest (header : Header) (r0 : OwnershipRequest) :
    Message.decodeBytes (Message.encode (.ownershipRequest header r0)) = some (.ownershipRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 49, 56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OwnershipRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_ownershipRequest header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_priceInput (header : Header) (r0 : PriceInput) :
    Message.decodeBytes (Message.encode (.priceInput header r0)) = some (.priceInput header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 73], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PriceInput.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_priceInput header r0

theorem Message.decodeBytes_liquidityProviderCommand (header : Header) (r0 : LiquidityProviderCommand) :
    Message.decodeBytes (Message.encode (.liquidityProviderCommand header r0)) = some (.liquidityProviderCommand header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 90], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ LiquidityProviderCommand.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_liquidityProviderCommand header r0

theorem Message.decodeBytes_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decodeBytes (Message.encode (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassStatusRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassStatusRequest header r0

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[113], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_newWholesaleOrder (header : Header) (r0 : NewWholesaleOrder) :
    Message.decodeBytes (Message.encode (.newWholesaleOrder header r0)) = some (.newWholesaleOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewWholesaleOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newWholesaleOrder header r0

theorem Message.decodeBytes_requestForImpliedExecution (header : Header) (r0 : RequestForImpliedExecution) :
    Message.decodeBytes (Message.encode (.requestForImpliedExecution header r0)) = some (.requestForImpliedExecution header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 54], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RequestForImpliedExecution.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_requestForImpliedExecution header r0

theorem Message.decodeBytes_crossOrder (header : Header) (r0 : CrossOrder) :
    Message.decodeBytes (Message.encode (.crossOrder header r0)) = some (.crossOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 55], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CrossOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_crossOrder header r0

theorem Message.decodeBytes_eRGCommand (header : Header) (r0 : ERGCommand) :
    Message.decodeBytes (Message.encode (.eRGCommand header r0)) = some (.eRGCommand header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ERGCommand.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eRGCommand header r0

theorem Message.decodeBytes_getRiskControls (header : Header) (r0 : GetRiskControls) :
    Message.decodeBytes (Message.encode (.getRiskControls header r0)) = some (.getRiskControls header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 48], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ GetRiskControls.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_getRiskControls header r0

theorem Message.decodeBytes_iOI (header : Header) (r0 : IOI) :
    Message.decodeBytes (Message.encode (.iOI header r0)) = some (.iOI header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[54], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ IOI.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_iOI header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_fundPriceInput (header : Header) (r0 : FundPriceInput) :
    Message.decodeBytes (Message.encode (.fundPriceInput header r0)) = some (.fundPriceInput header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 52, 52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ FundPriceInput.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_fundPriceInput header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | massQuote header r0 => exact Message.decodeBytes_massQuote header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | ownershipRequest header r0 => exact Message.decodeBytes_ownershipRequest header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | priceInput header r0 => exact Message.decodeBytes_priceInput header r0
  | liquidityProviderCommand header r0 => exact Message.decodeBytes_liquidityProviderCommand header r0
  | orderMassStatusRequest header r0 => exact Message.decodeBytes_orderMassStatusRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | newWholesaleOrder header r0 => exact Message.decodeBytes_newWholesaleOrder header r0
  | requestForImpliedExecution header r0 => exact Message.decodeBytes_requestForImpliedExecution header r0
  | crossOrder header r0 => exact Message.decodeBytes_crossOrder header r0
  | eRGCommand header r0 => exact Message.decodeBytes_eRGCommand header r0
  | getRiskControls header r0 => exact Message.decodeBytes_getRiskControls header r0
  | iOI header r0 => exact Message.decodeBytes_iOI header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | fundPriceInput header r0 => exact Message.decodeBytes_fundPriceInput header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.EuronextOptiqOrderentryFixV555Client
