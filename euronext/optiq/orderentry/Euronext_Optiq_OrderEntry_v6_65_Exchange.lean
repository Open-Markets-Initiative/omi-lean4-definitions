import Wire

/-!
# Euronext Order Entry v6.65, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.EuronextOptiqOrderentryFixV665Exchange

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Terminated 1  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.required [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
  pure { refSeqNum, refTagID, refMsgType, sessionRejectReason }

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
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, some_bind] <;> rfl

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

structure ExecutionReport where
  transactTime : Option (Terminated 1)  -- tag 60
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  clOrdID : Option (Terminated 1)  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  orderPriority : Option (Terminated 1)  -- tag 21004
  darkExecutionInstruction : Option (Terminated 1)  -- tag 20052
  price : Option (Terminated 1)  -- tag 44
  orderQty : Option (Terminated 1)  -- tag 38
  lastQty : Option (Terminated 1)  -- tag 32
  leavesQty : Terminated 1  -- tag 151
  execID : Terminated 1  -- tag 17
  parentExecID : Option (Terminated 1)  -- tag 21094
  parentSecurityID : Option (Terminated 1)  -- tag 21093
  stopPx : Option (Terminated 1)  -- tag 99
  undisclosedPrice : Option (Terminated 1)  -- tag 20004
  displayQty : Option (Terminated 1)  -- tag 1138
  undisclosedIcebergType : Option (Terminated 1)  -- tag 20005
  triggeredStopTimeInForce : Option (Terminated 1)  -- tag 20175
  quoteReqID : Option (Terminated 1)  -- tag 131
  massStatusReqID : Option (Terminated 1)  -- tag 584
  rFQAnswerIndicator : Option (Terminated 1)  -- tag 21037
  rFQConfirmationIndicator : Option (Terminated 1)  -- tag 21038
  conditionalOrderFlag : Option (Terminated 1)  -- tag 21800
  fRMARAMPLP : Option (Terminated 1)  -- tag 21801
  parentRegulatoryTradeID : Option (Terminated 1)  -- tag 21807
  noPartyIDs : Option (Terminated 1)  -- tag 453
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  partyRoleQualifi : Option (Terminated 1)  -- tag 2376
  orderOrigination : Option (Terminated 1)  -- tag 1724
  noOrderAttribut : Option (Terminated 1)  -- tag 2593
  orderAttributeTy : Option (Terminated 1)  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595
  lastCapacity : Option (Terminated 1)  -- tag 29
  minQty : Option (Terminated 1)  -- tag 110
  ackPhase : Option (Terminated 1)  -- tag 21013
  ackQualifiers : Option (Terminated 1)  -- tag 21014
  tradeType : Option (Terminated 1)  -- tag 21010
  execPhase : Option (Terminated 1)  -- tag 21023
  tradeQualifier : Option (Terminated 1)  -- tag 21080
  oEPartitionID : Option (Terminated 1)  -- tag 21019
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  eSCBMembership : Option (Terminated 1)  -- tag 21096
  evaluatedPrice : Option (Terminated 1)  -- tag 21802
  messagePriceNotation : Option (Terminated 1)  -- tag 21803
  finalSecurityID : Option (Terminated 1)  -- tag 21805
  finalExecID : Option (Terminated 1)  -- tag 21806
  noRegulatoryTradeIDs : Option (Terminated 1)  -- tag 1907
  regulatoryTradeID : Option (Terminated 1)  -- tag 1903
  regulatoryTradeIDType : Option (Terminated 1)  -- tag 1906
  regulatoryLegRefID : Option (Terminated 1)  -- tag 2411
  noLegs : Option (Terminated 1)  -- tag 555
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSo : Option (Terminated 1)  -- tag 603
  legLastPx : Option (Terminated 1)  -- tag 637
  legLastQty : Option (Terminated 1)  -- tag 1418
  legSide : Option (Terminated 1)  -- tag 624
  legExecID : Option (Terminated 1)  -- tag 1893
  legID : Option (Terminated 1)  -- tag 1788
  expireDate : Option (Terminated 1)  -- tag 432
  cumQty : Terminated 1  -- tag 14
  tradingSessionID : Option (Terminated 1)  -- tag 336
  ordType : Option (Terminated 1)  -- tag 40
  timeInForce : Option (Terminated 1)  -- tag 59
  noSides : Option (Terminated 1)  -- tag 552
  side : Option (Terminated 1)  -- tag 54
  clearingInstructi : Option (Terminated 1)  -- tag 577
  account : Option (Terminated 1)  -- tag 1
  accountCode : Option (Terminated 1)  -- tag 6399
  lPRole : Option (Terminated 1)  -- tag 20021
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  longClientID : Option (Terminated 1)  -- tag 21804
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  expireTime : Option (Terminated 1)  -- tag 126
  sTPAggressorIndicator : Option (Terminated 1)  -- tag 21015
  selfMatchPreventionID : Option (Terminated 1)  -- tag 2362
  disclosedQtyRandIndicator : Option (Terminated 1)  -- tag 21016
  cancelOnDisconnectionIndicator : Option (Terminated 1)  -- tag 21018
  pegPriceType : Option (Terminated 1)  -- tag 1094
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  errorCode : Option (Terminated 1)  -- tag 9955
  collarRejType : Option (Terminated 1)  -- tag 9962
  breachedCollarPrice : Option (Terminated 1)  -- tag 21001
  lISTransactionID : Option (Terminated 1)  -- tag 21085
  orderTolerablePrice : Option (Terminated 1)  -- tag 21822
  quoteType : Option (Terminated 1)  -- tag 537
  exposureDuration : Option (Terminated 1)  -- tag 1629
  numOfCompetitors : Option (Terminated 1)  -- tag 1913

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [54, 48] record.transactTime,
   Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.optional [50, 49, 48, 48, 52] record.orderPriority,
   Part.optional [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [52, 52] record.price,
   Part.optional [51, 56] record.orderQty,
   Part.optional [51, 50] record.lastQty,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 55] record.execID,
   Part.optional [50, 49, 48, 57, 52] record.parentExecID,
   Part.optional [50, 49, 48, 57, 51] record.parentSecurityID,
   Part.optional [57, 57] record.stopPx,
   Part.optional [50, 48, 48, 48, 52] record.undisclosedPrice,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [50, 48, 48, 48, 53] record.undisclosedIcebergType,
   Part.optional [50, 48, 49, 55, 53] record.triggeredStopTimeInForce,
   Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [53, 56, 52] record.massStatusReqID,
   Part.optional [50, 49, 48, 51, 55] record.rFQAnswerIndicator,
   Part.optional [50, 49, 48, 51, 56] record.rFQConfirmationIndicator,
   Part.optional [50, 49, 56, 48, 48] record.conditionalOrderFlag,
   Part.optional [50, 49, 56, 48, 49] record.fRMARAMPLP,
   Part.optional [50, 49, 56, 48, 55] record.parentRegulatoryTradeID,
   Part.optional [52, 53, 51] record.noPartyIDs,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 53, 57, 51] record.noOrderAttribut,
   Part.optional [50, 53, 57, 52] record.orderAttributeTy,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 48, 49, 51] record.ackPhase,
   Part.optional [50, 49, 48, 49, 52] record.ackQualifiers,
   Part.optional [50, 49, 48, 49, 48] record.tradeType,
   Part.optional [50, 49, 48, 50, 51] record.execPhase,
   Part.optional [50, 49, 48, 56, 48] record.tradeQualifier,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [50, 49, 48, 57, 54] record.eSCBMembership,
   Part.optional [50, 49, 56, 48, 50] record.evaluatedPrice,
   Part.optional [50, 49, 56, 48, 51] record.messagePriceNotation,
   Part.optional [50, 49, 56, 48, 53] record.finalSecurityID,
   Part.optional [50, 49, 56, 48, 54] record.finalExecID,
   Part.optional [49, 57, 48, 55] record.noRegulatoryTradeIDs,
   Part.optional [49, 57, 48, 51] record.regulatoryTradeID,
   Part.optional [49, 57, 48, 54] record.regulatoryTradeIDType,
   Part.optional [50, 52, 49, 49] record.regulatoryLegRefID,
   Part.optional [53, 53, 53] record.noLegs,
   Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSo,
   Part.optional [54, 51, 55] record.legLastPx,
   Part.optional [49, 52, 49, 56] record.legLastQty,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [49, 56, 57, 51] record.legExecID,
   Part.optional [49, 55, 56, 56] record.legID,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [49, 52] record.cumQty,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [52, 48] record.ordType,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [53, 53, 50] record.noSides,
   Part.optional [53, 52] record.side,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [49] record.account,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.optional [50, 48, 48, 50, 49] record.lPRole,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.optional [50, 49, 56, 48, 52] record.longClientID,
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 49, 48, 49, 53] record.sTPAggressorIndicator,
   Part.optional [50, 51, 54, 50] record.selfMatchPreventionID,
   Part.optional [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator,
   Part.optional [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.optional [57, 57, 54, 50] record.collarRejType,
   Part.optional [50, 49, 48, 48, 49] record.breachedCollarPrice,
   Part.optional [50, 49, 48, 56, 53] record.lISTransactionID,
   Part.optional [50, 49, 56, 50, 50] record.orderTolerablePrice,
   Part.optional [53, 51, 55] record.quoteType,
   Part.optional [49, 54, 50, 57] record.exposureDuration,
   Part.optional [49, 57, 49, 51] record.numOfCompetitors]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55]], [[51, 57]], [[50, 49, 48, 48, 52]], [[50, 48, 48, 53, 50]], [[52, 52]], [[51, 56]], [[51, 50]], [[49, 53, 49]], [[49, 55]], [[50, 49, 48, 57, 52]], [[50, 49, 48, 57, 51]], [[57, 57]], [[50, 48, 48, 48, 52]], [[49, 49, 51, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 49, 55, 53]], [[49, 51, 49]], [[53, 56, 52]], [[50, 49, 48, 51, 55]], [[50, 49, 48, 51, 56]], [[50, 49, 56, 48, 48]], [[50, 49, 56, 48, 49]], [[50, 49, 56, 48, 55]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 57]], [[49, 49, 48]], [[50, 49, 48, 49, 51]], [[50, 49, 48, 49, 52]], [[50, 49, 48, 49, 48]], [[50, 49, 48, 50, 51]], [[50, 49, 48, 56, 48]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[50, 49, 48, 57, 54]], [[50, 49, 56, 48, 50]], [[50, 49, 56, 48, 51]], [[50, 49, 56, 48, 53]], [[50, 49, 56, 48, 54]], [[49, 57, 48, 55]], [[49, 57, 48, 51]], [[49, 57, 48, 54]], [[50, 52, 49, 49]], [[53, 53, 53]], [[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 51, 55]], [[49, 52, 49, 56]], [[54, 50, 52]], [[49, 56, 57, 51]], [[49, 55, 56, 56]], [[52, 51, 50]], [[49, 52]], [[51, 51, 54]], [[52, 48]], [[53, 57]], [[53, 53, 50]], [[53, 52]], [[53, 55, 55]], [[49]], [[54, 51, 57, 57]], [[50, 48, 48, 50, 49]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[50, 49, 56, 48, 52]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[49, 50, 54]], [[50, 49, 48, 49, 53]], [[50, 51, 54, 50]], [[50, 49, 48, 49, 54]], [[50, 49, 48, 49, 56]], [[49, 48, 57, 52]], [[50, 49, 49]], [[57, 57, 53, 53]], [[57, 57, 54, 50]], [[50, 49, 48, 48, 49]], [[50, 49, 48, 56, 53]], [[50, 49, 56, 50, 50]], [[53, 51, 55]], [[49, 54, 50, 57]], [[49, 57, 49, 51]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let transactTime ← readOptional [54, 48] tokens
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let orderPriority ← readOptional [50, 49, 48, 48, 52] tokens
  let darkExecutionInstruction ← readOptional [50, 48, 48, 53, 50] tokens
  let price ← readOptional [52, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let parentExecID ← readOptional [50, 49, 48, 57, 52] tokens
  let parentSecurityID ← readOptional [50, 49, 48, 57, 51] tokens
  let stopPx ← readOptional [57, 57] tokens
  let undisclosedPrice ← readOptional [50, 48, 48, 48, 52] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let undisclosedIcebergType ← readOptional [50, 48, 48, 48, 53] tokens
  let triggeredStopTimeInForce ← readOptional [50, 48, 49, 55, 53] tokens
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let massStatusReqID ← readOptional [53, 56, 52] tokens
  let rFQAnswerIndicator ← readOptional [50, 49, 48, 51, 55] tokens
  let rFQConfirmationIndicator ← readOptional [50, 49, 48, 51, 56] tokens
  let conditionalOrderFlag ← readOptional [50, 49, 56, 48, 48] tokens
  let fRMARAMPLP ← readOptional [50, 49, 56, 48, 49] tokens
  let parentRegulatoryTradeID ← readOptional [50, 49, 56, 48, 55] tokens
  let noPartyIDs ← readOptional [52, 53, 51] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let partyRoleQualifi ← readOptional [50, 51, 55, 54] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let noOrderAttribut ← readOptional [50, 53, 57, 51] tokens
  let orderAttributeTy ← readOptional [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let ackPhase ← readOptional [50, 49, 48, 49, 51] tokens
  let ackQualifiers ← readOptional [50, 49, 48, 49, 52] tokens
  let tradeType ← readOptional [50, 49, 48, 49, 48] tokens
  let execPhase ← readOptional [50, 49, 48, 50, 51] tokens
  let tradeQualifier ← readOptional [50, 49, 48, 56, 48] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let eSCBMembership ← readOptional [50, 49, 48, 57, 54] tokens
  let evaluatedPrice ← readOptional [50, 49, 56, 48, 50] tokens
  let messagePriceNotation ← readOptional [50, 49, 56, 48, 51] tokens
  let finalSecurityID ← readOptional [50, 49, 56, 48, 53] tokens
  let finalExecID ← readOptional [50, 49, 56, 48, 54] tokens
  let noRegulatoryTradeIDs ← readOptional [49, 57, 48, 55] tokens
  let regulatoryTradeID ← readOptional [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readOptional [49, 57, 48, 54] tokens
  let regulatoryLegRefID ← readOptional [50, 52, 49, 49] tokens
  let noLegs ← readOptional [53, 53, 53] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSo ← readOptional [54, 48, 51] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  let legLastQty ← readOptional [49, 52, 49, 56] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legExecID ← readOptional [49, 56, 57, 51] tokens
  let legID ← readOptional [49, 55, 56, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let cumQty ← readRequired [49, 52] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let ordType ← readOptional [52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let noSides ← readOptional [53, 53, 50] tokens
  let side ← readOptional [53, 52] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let account ← readOptional [49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let lPRole ← readOptional [50, 48, 48, 50, 49] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let longClientID ← readOptional [50, 49, 56, 48, 52] tokens
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let sTPAggressorIndicator ← readOptional [50, 49, 48, 49, 53] tokens
  let selfMatchPreventionID ← readOptional [50, 51, 54, 50] tokens
  let disclosedQtyRandIndicator ← readOptional [50, 49, 48, 49, 54] tokens
  let cancelOnDisconnectionIndicator ← readOptional [50, 49, 48, 49, 56] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let collarRejType ← readOptional [57, 57, 54, 50] tokens
  let breachedCollarPrice ← readOptional [50, 49, 48, 48, 49] tokens
  let lISTransactionID ← readOptional [50, 49, 48, 56, 53] tokens
  let orderTolerablePrice ← readOptional [50, 49, 56, 50, 50] tokens
  let quoteType ← readOptional [53, 51, 55] tokens
  let exposureDuration ← readOptional [49, 54, 50, 57] tokens
  let numOfCompetitors ← readOptional [49, 57, 49, 51] tokens
  pure { transactTime, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, securityID, securityIDSource, eMM, orderID, ordStatus, orderPriority, darkExecutionInstruction, price, orderQty, lastQty, leavesQty, execID, parentExecID, parentSecurityID, stopPx, undisclosedPrice, displayQty, undisclosedIcebergType, triggeredStopTimeInForce, quoteReqID, massStatusReqID, rFQAnswerIndicator, rFQConfirmationIndicator, conditionalOrderFlag, fRMARAMPLP, parentRegulatoryTradeID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, lastCapacity, minQty, ackPhase, ackQualifiers, tradeType, execPhase, tradeQualifier, oEPartitionID, logicalAccessID, eSCBMembership, evaluatedPrice, messagePriceNotation, finalSecurityID, finalExecID, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, regulatoryLegRefID, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legLastPx, legLastQty, legSide, legExecID, legID, expireDate, cumQty, tradingSessionID, ordType, timeInForce, noSides, side, clearingInstructi, account, accountCode, lPRole, technicalOrdType, postingAction, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, expireTime, sTPAggressorIndicator, selfMatchPreventionID, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, errorCode, collarRejType, breachedCollarPrice, lISTransactionID, orderTolerablePrice, quoteType, exposureDuration, numOfCompetitors }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderPriority := readOptional_part [50, 49, 48, 48, 52] record.orderPriority tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have darkExecutionInstruction := readOptional_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have parentExecID := readOptional_part [50, 49, 48, 57, 52] record.parentExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have parentSecurityID := readOptional_part [50, 49, 48, 57, 51] record.parentSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have undisclosedPrice := readOptional_part [50, 48, 48, 48, 52] record.undisclosedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have undisclosedIcebergType := readOptional_part [50, 48, 48, 48, 53] record.undisclosedIcebergType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have triggeredStopTimeInForce := readOptional_part [50, 48, 49, 55, 53] record.triggeredStopTimeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have massStatusReqID := readOptional_part [53, 56, 52] record.massStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have rFQAnswerIndicator := readOptional_part [50, 49, 48, 51, 55] record.rFQAnswerIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have rFQConfirmationIndicator := readOptional_part [50, 49, 48, 51, 56] record.rFQConfirmationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have conditionalOrderFlag := readOptional_part [50, 49, 56, 48, 48] record.conditionalOrderFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have fRMARAMPLP := readOptional_part [50, 49, 56, 48, 49] record.fRMARAMPLP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have parentRegulatoryTradeID := readOptional_part [50, 49, 56, 48, 55] record.parentRegulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have partyRoleQualifi := readOptional_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have ackPhase := readOptional_part [50, 49, 48, 49, 51] record.ackPhase tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have ackQualifiers := readOptional_part [50, 49, 48, 49, 52] record.ackQualifiers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have tradeType := readOptional_part [50, 49, 48, 49, 48] record.tradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have execPhase := readOptional_part [50, 49, 48, 50, 51] record.execPhase tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have tradeQualifier := readOptional_part [50, 49, 48, 56, 48] record.tradeQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have eSCBMembership := readOptional_part [50, 49, 48, 57, 54] record.eSCBMembership tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have evaluatedPrice := readOptional_part [50, 49, 56, 48, 50] record.evaluatedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have messagePriceNotation := readOptional_part [50, 49, 56, 48, 51] record.messagePriceNotation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have finalSecurityID := readOptional_part [50, 49, 56, 48, 53] record.finalSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have finalExecID := readOptional_part [50, 49, 56, 48, 54] record.finalExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have noRegulatoryTradeIDs := readOptional_part [49, 57, 48, 55] record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have regulatoryTradeID := readOptional_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have regulatoryTradeIDType := readOptional_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have regulatoryLegRefID := readOptional_part [50, 52, 49, 49] record.regulatoryLegRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have noLegs := readOptional_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have legSecurityID := readOptional_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have legSecurityIDSo := readOptional_part [54, 48, 51] record.legSecurityIDSo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have legLastPx := readOptional_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have legLastQty := readOptional_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have legExecID := readOptional_part [49, 56, 57, 51] record.legExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have legID := readOptional_part [49, 55, 56, 56] record.legID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 72 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 73 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 74 (by decide +kernel)))
  have noSides := readOptional_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 75 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 76 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 77 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 78 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 79 (by decide +kernel)))
  have lPRole := readOptional_part [50, 48, 48, 50, 49] record.lPRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 80 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 81 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 82 (by decide +kernel)))
  have longClientID := readOptional_part [50, 49, 56, 48, 52] record.longClientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 83 (by decide +kernel)))
  have noNestedPartyIDs := readOptional_part [53, 51, 57] record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 84 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 85 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 86 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 87 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 88 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 89 (by decide +kernel)))
  have sTPAggressorIndicator := readOptional_part [50, 49, 48, 49, 53] record.sTPAggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 90 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 51, 54, 50] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 91 (by decide +kernel)))
  have disclosedQtyRandIndicator := readOptional_part [50, 49, 48, 49, 54] record.disclosedQtyRandIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 92 (by decide +kernel)))
  have cancelOnDisconnectionIndicator := readOptional_part [50, 49, 48, 49, 56] record.cancelOnDisconnectionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 93 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 94 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 95 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 96 (by decide +kernel)))
  have collarRejType := readOptional_part [57, 57, 54, 50] record.collarRejType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 97 (by decide +kernel)))
  have breachedCollarPrice := readOptional_part [50, 49, 48, 48, 49] record.breachedCollarPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 98 (by decide +kernel)))
  have lISTransactionID := readOptional_part [50, 49, 48, 56, 53] record.lISTransactionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 99 (by decide +kernel)))
  have orderTolerablePrice := readOptional_part [50, 49, 56, 50, 50] record.orderTolerablePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 100 (by decide +kernel)))
  have quoteType := readOptional_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 101 (by decide +kernel)))
  have exposureDuration := readOptional_part [49, 54, 50, 57] record.exposureDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 102 (by decide +kernel)))
  have numOfCompetitors := readOptional_part [49, 57, 49, 51] record.numOfCompetitors tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 103 (by decide +kernel)))
  simp only [ExecutionReport.decode, transactTime, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, securityID, securityIDSource, eMM, orderID, ordStatus, orderPriority, darkExecutionInstruction, price, orderQty, lastQty, leavesQty, execID, parentExecID, parentSecurityID, stopPx, undisclosedPrice, displayQty, undisclosedIcebergType, triggeredStopTimeInForce, quoteReqID, massStatusReqID, rFQAnswerIndicator, rFQConfirmationIndicator, conditionalOrderFlag, fRMARAMPLP, parentRegulatoryTradeID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, lastCapacity, minQty, ackPhase, ackQualifiers, tradeType, execPhase, tradeQualifier, oEPartitionID, logicalAccessID, eSCBMembership, evaluatedPrice, messagePriceNotation, finalSecurityID, finalExecID, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, regulatoryLegRefID, noLegs, legSymbol, legSecurityID, legSecurityIDSo, legLastPx, legLastQty, legSide, legExecID, legID, expireDate, cumQty, tradingSessionID, ordType, timeInForce, noSides, side, clearingInstructi, account, accountCode, lPRole, technicalOrdType, postingAction, longClientID, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, expireTime, sTPAggressorIndicator, selfMatchPreventionID, disclosedQtyRandIndicator, cancelOnDisconnectionIndicator, pegPriceType, pegOffsetValue, errorCode, collarRejType, breachedCollarPrice, lISTransactionID, orderTolerablePrice, quoteType, exposureDuration, numOfCompetitors, some_bind] <;> rfl

structure ExecutionReportNew

def ExecutionReportNew.parts (_ : ExecutionReportNew) : List Part :=
  []

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (_ : List Token) : Option ExecutionReportNew := some {}

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  rfl

structure ExecutionReportCancelledbyReactor where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportCancelledbyReactor.parts (record : ExecutionReportCancelledbyReactor) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportCancelledbyReactor.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportCancelledbyReactor.shape (record : ExecutionReportCancelledbyReactor) : record.parts.map Part.tags = ExecutionReportCancelledbyReactor.tags := rfl

def ExecutionReportCancelledbyReactor.decode (tokens : List Token) : Option ExecutionReportCancelledbyReactor := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportCancelledbyReactor.decode_agrees (record : ExecutionReportCancelledbyReactor) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelledbyReactor.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelledbyReactor.decode tokens = some record := by
  have distinct : ExecutionReportCancelledbyReactor.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportCancelledbyReactor.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportCrossOrderAck

def ExecutionReportCrossOrderAck.parts (_ : ExecutionReportCrossOrderAck) : List Part :=
  []

def ExecutionReportCrossOrderAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportCrossOrderAck.shape (record : ExecutionReportCrossOrderAck) : record.parts.map Part.tags = ExecutionReportCrossOrderAck.tags := rfl

def ExecutionReportCrossOrderAck.decode (_ : List Token) : Option ExecutionReportCrossOrderAck := some {}

theorem ExecutionReportCrossOrderAck.decode_agrees (record : ExecutionReportCrossOrderAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportCrossOrderAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCrossOrderAck.decode tokens = some record := by
  rfl

structure ExecutionReportDoneForDay

def ExecutionReportDoneForDay.parts (_ : ExecutionReportDoneForDay) : List Part :=
  []

def ExecutionReportDoneForDay.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportDoneForDay.shape (record : ExecutionReportDoneForDay) : record.parts.map Part.tags = ExecutionReportDoneForDay.tags := rfl

def ExecutionReportDoneForDay.decode (_ : List Token) : Option ExecutionReportDoneForDay := some {}

theorem ExecutionReportDoneForDay.decode_agrees (record : ExecutionReportDoneForDay) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportDoneForDay.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportDoneForDay.decode tokens = some record := by
  rfl

structure ExecutionReportCancelled where
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportCancelled.parts (record : ExecutionReportCancelled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text]

def ExecutionReportCancelled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[53, 56]]]

theorem ExecutionReportCancelled.shape (record : ExecutionReportCancelled) : record.parts.map Part.tags = ExecutionReportCancelled.tags := rfl

def ExecutionReportCancelled.decode (tokens : List Token) : Option ExecutionReportCancelled := do
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  pure { origClOrdID, text }

theorem ExecutionReportCancelled.decode_agrees (record : ExecutionReportCancelled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelled.decode tokens = some record := by
  have distinct : ExecutionReportCancelled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCancelled.decode, origClOrdID, text, some_bind] <;> rfl

structure ExecutionReportReplaced where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportReplaced.parts (record : ExecutionReportReplaced) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportReplaced.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportReplaced.shape (record : ExecutionReportReplaced) : record.parts.map Part.tags = ExecutionReportReplaced.tags := rfl

def ExecutionReportReplaced.decode (tokens : List Token) : Option ExecutionReportReplaced := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportReplaced.decode_agrees (record : ExecutionReportReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplaced.decode tokens = some record := by
  have distinct : ExecutionReportReplaced.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportReplaced.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportRejected where
  ordRejReason : Option (Terminated 1)  -- tag 103
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[49, 48, 51]], [[53, 56]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { ordRejReason, text }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, ordRejReason, text, some_bind] <;> rfl

structure ExecutionReportCancelledbySTP where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportCancelledbySTP.parts (record : ExecutionReportCancelledbySTP) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportCancelledbySTP.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportCancelledbySTP.shape (record : ExecutionReportCancelledbySTP) : record.parts.map Part.tags = ExecutionReportCancelledbySTP.tags := rfl

def ExecutionReportCancelledbySTP.decode (tokens : List Token) : Option ExecutionReportCancelledbySTP := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportCancelledbySTP.decode_agrees (record : ExecutionReportCancelledbySTP) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelledbySTP.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelledbySTP.decode tokens = some record := by
  have distinct : ExecutionReportCancelledbySTP.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportCancelledbySTP.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportCancelledbyCOD where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportCancelledbyCOD.parts (record : ExecutionReportCancelledbyCOD) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportCancelledbyCOD.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportCancelledbyCOD.shape (record : ExecutionReportCancelledbyCOD) : record.parts.map Part.tags = ExecutionReportCancelledbyCOD.tags := rfl

def ExecutionReportCancelledbyCOD.decode (tokens : List Token) : Option ExecutionReportCancelledbyCOD := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportCancelledbyCOD.decode_agrees (record : ExecutionReportCancelledbyCOD) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelledbyCOD.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelledbyCOD.decode tokens = some record := by
  have distinct : ExecutionReportCancelledbyCOD.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportCancelledbyCOD.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportConditionalCancelled where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportConditionalCancelled.parts (record : ExecutionReportConditionalCancelled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportConditionalCancelled.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportConditionalCancelled.shape (record : ExecutionReportConditionalCancelled) : record.parts.map Part.tags = ExecutionReportConditionalCancelled.tags := rfl

def ExecutionReportConditionalCancelled.decode (tokens : List Token) : Option ExecutionReportConditionalCancelled := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportConditionalCancelled.decode_agrees (record : ExecutionReportConditionalCancelled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportConditionalCancelled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportConditionalCancelled.decode tokens = some record := by
  have distinct : ExecutionReportConditionalCancelled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportConditionalCancelled.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportCollarConfirmationAck

def ExecutionReportCollarConfirmationAck.parts (_ : ExecutionReportCollarConfirmationAck) : List Part :=
  []

def ExecutionReportCollarConfirmationAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportCollarConfirmationAck.shape (record : ExecutionReportCollarConfirmationAck) : record.parts.map Part.tags = ExecutionReportCollarConfirmationAck.tags := rfl

def ExecutionReportCollarConfirmationAck.decode (_ : List Token) : Option ExecutionReportCollarConfirmationAck := some {}

theorem ExecutionReportCollarConfirmationAck.decode_agrees (record : ExecutionReportCollarConfirmationAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportCollarConfirmationAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCollarConfirmationAck.decode tokens = some record := by
  rfl

structure ExecutionReportRefilledIcebergAck

def ExecutionReportRefilledIcebergAck.parts (_ : ExecutionReportRefilledIcebergAck) : List Part :=
  []

def ExecutionReportRefilledIcebergAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportRefilledIcebergAck.shape (record : ExecutionReportRefilledIcebergAck) : record.parts.map Part.tags = ExecutionReportRefilledIcebergAck.tags := rfl

def ExecutionReportRefilledIcebergAck.decode (_ : List Token) : Option ExecutionReportRefilledIcebergAck := some {}

theorem ExecutionReportRefilledIcebergAck.decode_agrees (record : ExecutionReportRefilledIcebergAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportRefilledIcebergAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRefilledIcebergAck.decode tokens = some record := by
  rfl

structure ExecutionReportLPCancelRFQCancellation where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportLPCancelRFQCancellation.parts (record : ExecutionReportLPCancelRFQCancellation) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportLPCancelRFQCancellation.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportLPCancelRFQCancellation.shape (record : ExecutionReportLPCancelRFQCancellation) : record.parts.map Part.tags = ExecutionReportLPCancelRFQCancellation.tags := rfl

def ExecutionReportLPCancelRFQCancellation.decode (tokens : List Token) : Option ExecutionReportLPCancelRFQCancellation := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportLPCancelRFQCancellation.decode_agrees (record : ExecutionReportLPCancelRFQCancellation) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportLPCancelRFQCancellation.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportLPCancelRFQCancellation.decode tokens = some record := by
  have distinct : ExecutionReportLPCancelRFQCancellation.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportLPCancelRFQCancellation.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportQuoteKnockOut

def ExecutionReportQuoteKnockOut.parts (_ : ExecutionReportQuoteKnockOut) : List Part :=
  []

def ExecutionReportQuoteKnockOut.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportQuoteKnockOut.shape (record : ExecutionReportQuoteKnockOut) : record.parts.map Part.tags = ExecutionReportQuoteKnockOut.tags := rfl

def ExecutionReportQuoteKnockOut.decode (_ : List Token) : Option ExecutionReportQuoteKnockOut := some {}

theorem ExecutionReportQuoteKnockOut.decode_agrees (record : ExecutionReportQuoteKnockOut) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportQuoteKnockOut.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportQuoteKnockOut.decode tokens = some record := by
  rfl

structure ExecutionReportIcebergMinSizeTransform

def ExecutionReportIcebergMinSizeTransform.parts (_ : ExecutionReportIcebergMinSizeTransform) : List Part :=
  []

def ExecutionReportIcebergMinSizeTransform.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportIcebergMinSizeTransform.shape (record : ExecutionReportIcebergMinSizeTransform) : record.parts.map Part.tags = ExecutionReportIcebergMinSizeTransform.tags := rfl

def ExecutionReportIcebergMinSizeTransform.decode (_ : List Token) : Option ExecutionReportIcebergMinSizeTransform := some {}

theorem ExecutionReportIcebergMinSizeTransform.decode_agrees (record : ExecutionReportIcebergMinSizeTransform) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportIcebergMinSizeTransform.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportIcebergMinSizeTransform.decode tokens = some record := by
  rfl

structure ExecutionReportCreatedbyMarketOperations

def ExecutionReportCreatedbyMarketOperations.parts (_ : ExecutionReportCreatedbyMarketOperations) : List Part :=
  []

def ExecutionReportCreatedbyMarketOperations.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportCreatedbyMarketOperations.shape (record : ExecutionReportCreatedbyMarketOperations) : record.parts.map Part.tags = ExecutionReportCreatedbyMarketOperations.tags := rfl

def ExecutionReportCreatedbyMarketOperations.decode (_ : List Token) : Option ExecutionReportCreatedbyMarketOperations := some {}

theorem ExecutionReportCreatedbyMarketOperations.decode_agrees (record : ExecutionReportCreatedbyMarketOperations) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportCreatedbyMarketOperations.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCreatedbyMarketOperations.decode tokens = some record := by
  rfl

structure ExecutionReportRFQAck

def ExecutionReportRFQAck.parts (_ : ExecutionReportRFQAck) : List Part :=
  []

def ExecutionReportRFQAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportRFQAck.shape (record : ExecutionReportRFQAck) : record.parts.map Part.tags = ExecutionReportRFQAck.tags := rfl

def ExecutionReportRFQAck.decode (_ : List Token) : Option ExecutionReportRFQAck := some {}

theorem ExecutionReportRFQAck.decode_agrees (record : ExecutionReportRFQAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportRFQAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRFQAck.decode tokens = some record := by
  rfl

structure ExecutionReportOwnershipRequestAck

def ExecutionReportOwnershipRequestAck.parts (_ : ExecutionReportOwnershipRequestAck) : List Part :=
  []

def ExecutionReportOwnershipRequestAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportOwnershipRequestAck.shape (record : ExecutionReportOwnershipRequestAck) : record.parts.map Part.tags = ExecutionReportOwnershipRequestAck.tags := rfl

def ExecutionReportOwnershipRequestAck.decode (_ : List Token) : Option ExecutionReportOwnershipRequestAck := some {}

theorem ExecutionReportOwnershipRequestAck.decode_agrees (record : ExecutionReportOwnershipRequestAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportOwnershipRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOwnershipRequestAck.decode tokens = some record := by
  rfl

structure ExecutionReportOrderMassStatusRequestAck

def ExecutionReportOrderMassStatusRequestAck.parts (_ : ExecutionReportOrderMassStatusRequestAck) : List Part :=
  []

def ExecutionReportOrderMassStatusRequestAck.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportOrderMassStatusRequestAck.shape (record : ExecutionReportOrderMassStatusRequestAck) : record.parts.map Part.tags = ExecutionReportOrderMassStatusRequestAck.tags := rfl

def ExecutionReportOrderMassStatusRequestAck.decode (_ : List Token) : Option ExecutionReportOrderMassStatusRequestAck := some {}

theorem ExecutionReportOrderMassStatusRequestAck.decode_agrees (record : ExecutionReportOrderMassStatusRequestAck) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportOrderMassStatusRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOrderMassStatusRequestAck.decode tokens = some record := by
  rfl

structure ExecutionReportCancelledFSPLimit where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportCancelledFSPLimit.parts (record : ExecutionReportCancelledFSPLimit) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportCancelledFSPLimit.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportCancelledFSPLimit.shape (record : ExecutionReportCancelledFSPLimit) : record.parts.map Part.tags = ExecutionReportCancelledFSPLimit.tags := rfl

def ExecutionReportCancelledFSPLimit.decode (tokens : List Token) : Option ExecutionReportCancelledFSPLimit := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportCancelledFSPLimit.decode_agrees (record : ExecutionReportCancelledFSPLimit) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelledFSPLimit.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelledFSPLimit.decode tokens = some record := by
  have distinct : ExecutionReportCancelledFSPLimit.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportCancelledFSPLimit.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportExpired where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportExpired.parts (record : ExecutionReportExpired) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportExpired.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportExpired.shape (record : ExecutionReportExpired) : record.parts.map Part.tags = ExecutionReportExpired.tags := rfl

def ExecutionReportExpired.decode (tokens : List Token) : Option ExecutionReportExpired := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportExpired.decode_agrees (record : ExecutionReportExpired) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportExpired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportExpired.decode tokens = some record := by
  have distinct : ExecutionReportExpired.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportExpired.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportRestated where
  execRestatementReason : Option (Terminated 1)  -- tag 378

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  pure { execRestatementReason }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, execRestatementReason, some_bind] <;> rfl

structure ExecutionReportTrade where
  lastPx : Option (Terminated 1)  -- tag 31
  contraBroker : Option (Terminated 1)  -- tag 375
  noContraBrokers : Option (Terminated 1)  -- tag 382
  trdMatchID : Option (Terminated 1)  -- tag 880
  lastLiquidityInd : Option (Terminated 1)  -- tag 851

def ExecutionReportTrade.parts (record : ExecutionReportTrade) : List Part :=
  [Part.optional [51, 49] record.lastPx,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [56, 53, 49] record.lastLiquidityInd]

def ExecutionReportTrade.tags : List (List (List UInt8)) :=
  [[[51, 49]], [[51, 55, 53]], [[51, 56, 50]], [[56, 56, 48]], [[56, 53, 49]]]

theorem ExecutionReportTrade.shape (record : ExecutionReportTrade) : record.parts.map Part.tags = ExecutionReportTrade.tags := rfl

def ExecutionReportTrade.decode (tokens : List Token) : Option ExecutionReportTrade := do
  let lastPx ← readOptional [51, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  pure { lastPx, contraBroker, noContraBrokers, trdMatchID, lastLiquidityInd }

theorem ExecutionReportTrade.decode_agrees (record : ExecutionReportTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTrade.decode tokens = some record := by
  have distinct : ExecutionReportTrade.tags.flatten.Nodup := by decide +kernel
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportTrade.decode, lastPx, contraBroker, noContraBrokers, trdMatchID, lastLiquidityInd, some_bind] <;> rfl

structure ExecutionReportCancelTrade where
  execRefID : Option (Terminated 1)  -- tag 19
  lastPx : Option (Terminated 1)  -- tag 31

def ExecutionReportCancelTrade.parts (record : ExecutionReportCancelTrade) : List Part :=
  [Part.optional [49, 57] record.execRefID,
   Part.optional [51, 49] record.lastPx]

def ExecutionReportCancelTrade.tags : List (List (List UInt8)) :=
  [[[49, 57]], [[51, 49]]]

theorem ExecutionReportCancelTrade.shape (record : ExecutionReportCancelTrade) : record.parts.map Part.tags = ExecutionReportCancelTrade.tags := rfl

def ExecutionReportCancelTrade.decode (tokens : List Token) : Option ExecutionReportCancelTrade := do
  let execRefID ← readOptional [49, 57] tokens
  let lastPx ← readOptional [51, 49] tokens
  pure { execRefID, lastPx }

theorem ExecutionReportCancelTrade.decode_agrees (record : ExecutionReportCancelTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelTrade.decode tokens = some record := by
  have distinct : ExecutionReportCancelTrade.tags.flatten.Nodup := by decide +kernel
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCancelTrade.decode, execRefID, lastPx, some_bind] <;> rfl

structure ExecutionReportOrderStatus

def ExecutionReportOrderStatus.parts (_ : ExecutionReportOrderStatus) : List Part :=
  []

def ExecutionReportOrderStatus.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportOrderStatus.shape (record : ExecutionReportOrderStatus) : record.parts.map Part.tags = ExecutionReportOrderStatus.tags := rfl

def ExecutionReportOrderStatus.decode (_ : List Token) : Option ExecutionReportOrderStatus := some {}

theorem ExecutionReportOrderStatus.decode_agrees (record : ExecutionReportOrderStatus) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportOrderStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOrderStatus.decode tokens = some record := by
  rfl

structure ExecutionReportTriggeredbySystem

def ExecutionReportTriggeredbySystem.parts (_ : ExecutionReportTriggeredbySystem) : List Part :=
  []

def ExecutionReportTriggeredbySystem.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportTriggeredbySystem.shape (record : ExecutionReportTriggeredbySystem) : record.parts.map Part.tags = ExecutionReportTriggeredbySystem.tags := rfl

def ExecutionReportTriggeredbySystem.decode (_ : List Token) : Option ExecutionReportTriggeredbySystem := some {}

theorem ExecutionReportTriggeredbySystem.decode_agrees (record : ExecutionReportTriggeredbySystem) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportTriggeredbySystem.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTriggeredbySystem.decode tokens = some record := by
  rfl

structure ExecutionReportCancelledbyMarketOperations where
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportCancelledbyMarketOperations.parts (record : ExecutionReportCancelledbyMarketOperations) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text]

def ExecutionReportCancelledbyMarketOperations.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[53, 56]]]

theorem ExecutionReportCancelledbyMarketOperations.shape (record : ExecutionReportCancelledbyMarketOperations) : record.parts.map Part.tags = ExecutionReportCancelledbyMarketOperations.tags := rfl

def ExecutionReportCancelledbyMarketOperations.decode (tokens : List Token) : Option ExecutionReportCancelledbyMarketOperations := do
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  pure { origClOrdID, text }

theorem ExecutionReportCancelledbyMarketOperations.decode_agrees (record : ExecutionReportCancelledbyMarketOperations) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCancelledbyMarketOperations.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCancelledbyMarketOperations.decode tokens = some record := by
  have distinct : ExecutionReportCancelledbyMarketOperations.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCancelledbyMarketOperations.decode, origClOrdID, text, some_bind] <;> rfl

structure MassQuoteAck where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  quoteID : Terminated 1  -- tag 117
  quoteStatus : Terminated 1  -- tag 297
  accountCode : Terminated 1  -- tag 6399
  lPRole : Terminated 1  -- tag 20021
  clearingInstructi : Option (Terminated 1)  -- tag 577
  account : Option (Terminated 1)  -- tag 1
  technicalOrdType : Option (Terminated 1)  -- tag 9941
  postingAction : Option (Terminated 1)  -- tag 7443
  ackQualifiers : Option (Terminated 1)  -- tag 21014
  quoteSetID : Option (Terminated 1)  -- tag 302
  totNoQuotEntries : Option (Terminated 1)  -- tag 304
  noQuoteEntries : Option (Terminated 1)  -- tag 295
  quoteEntryID : Option (Terminated 1)  -- tag 299
  bidQuoteID : Option (Terminated 1)  -- tag 1747
  offerQuoteID : Option (Terminated 1)  -- tag 1748
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  bidErrorCode : Option (Terminated 1)  -- tag 9934
  offerErrorCode : Option (Terminated 1)  -- tag 9935
  buyRevisionIndicator : Option (Terminated 1)  -- tag 21008
  sellRevisionIndicator : Option (Terminated 1)  -- tag 21009

def MassQuoteAck.parts (record : MassQuoteAck) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [49, 49, 55] record.quoteID,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.required [54, 51, 57, 57] record.accountCode,
   Part.required [50, 48, 48, 50, 49] record.lPRole,
   Part.optional [53, 55, 55] record.clearingInstructi,
   Part.optional [49] record.account,
   Part.optional [57, 57, 52, 49] record.technicalOrdType,
   Part.optional [55, 52, 52, 51] record.postingAction,
   Part.optional [50, 49, 48, 49, 52] record.ackQualifiers,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [51, 48, 52] record.totNoQuotEntries,
   Part.optional [50, 57, 53] record.noQuoteEntries,
   Part.optional [50, 57, 57] record.quoteEntryID,
   Part.optional [49, 55, 52, 55] record.bidQuoteID,
   Part.optional [49, 55, 52, 56] record.offerQuoteID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [57, 57, 51, 52] record.bidErrorCode,
   Part.optional [57, 57, 51, 53] record.offerErrorCode,
   Part.optional [50, 49, 48, 48, 56] record.buyRevisionIndicator,
   Part.optional [50, 49, 48, 48, 57] record.sellRevisionIndicator]

def MassQuoteAck.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[49, 49, 55]], [[50, 57, 55]], [[54, 51, 57, 57]], [[50, 48, 48, 50, 49]], [[53, 55, 55]], [[49]], [[57, 57, 52, 49]], [[55, 52, 52, 51]], [[50, 49, 48, 49, 52]], [[51, 48, 50]], [[51, 48, 52]], [[50, 57, 53]], [[50, 57, 57]], [[49, 55, 52, 55]], [[49, 55, 52, 56]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[57, 57, 51, 52]], [[57, 57, 51, 53]], [[50, 49, 48, 48, 56]], [[50, 49, 48, 48, 57]]]

theorem MassQuoteAck.shape (record : MassQuoteAck) : record.parts.map Part.tags = MassQuoteAck.tags := rfl

def MassQuoteAck.decode (tokens : List Token) : Option MassQuoteAck := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let accountCode ← readRequired [54, 51, 57, 57] tokens
  let lPRole ← readRequired [50, 48, 48, 50, 49] tokens
  let clearingInstructi ← readOptional [53, 55, 55] tokens
  let account ← readOptional [49] tokens
  let technicalOrdType ← readOptional [57, 57, 52, 49] tokens
  let postingAction ← readOptional [55, 52, 52, 51] tokens
  let ackQualifiers ← readOptional [50, 49, 48, 49, 52] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let totNoQuotEntries ← readOptional [51, 48, 52] tokens
  let noQuoteEntries ← readOptional [50, 57, 53] tokens
  let quoteEntryID ← readOptional [50, 57, 57] tokens
  let bidQuoteID ← readOptional [49, 55, 52, 55] tokens
  let offerQuoteID ← readOptional [49, 55, 52, 56] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let bidErrorCode ← readOptional [57, 57, 51, 52] tokens
  let offerErrorCode ← readOptional [57, 57, 51, 53] tokens
  let buyRevisionIndicator ← readOptional [50, 49, 48, 48, 56] tokens
  let sellRevisionIndicator ← readOptional [50, 49, 48, 48, 57] tokens
  pure { clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteID, quoteStatus, accountCode, lPRole, clearingInstructi, account, technicalOrdType, postingAction, ackQualifiers, quoteSetID, totNoQuotEntries, noQuoteEntries, quoteEntryID, bidQuoteID, offerQuoteID, securityID, securityIDSource, eMM, bidErrorCode, offerErrorCode, buyRevisionIndicator, sellRevisionIndicator }

theorem MassQuoteAck.decode_agrees (record : MassQuoteAck) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuoteAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuoteAck.decode tokens = some record := by
  have distinct : MassQuoteAck.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have accountCode := readRequired_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lPRole := readRequired_part [50, 48, 48, 50, 49] record.lPRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clearingInstructi := readOptional_part [53, 55, 55] record.clearingInstructi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have technicalOrdType := readOptional_part [57, 57, 52, 49] record.technicalOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have postingAction := readOptional_part [55, 52, 52, 51] record.postingAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ackQualifiers := readOptional_part [50, 49, 48, 49, 52] record.ackQualifiers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have totNoQuotEntries := readOptional_part [51, 48, 52] record.totNoQuotEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noQuoteEntries := readOptional_part [50, 57, 53] record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have quoteEntryID := readOptional_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have bidQuoteID := readOptional_part [49, 55, 52, 55] record.bidQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have offerQuoteID := readOptional_part [49, 55, 52, 56] record.offerQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have bidErrorCode := readOptional_part [57, 57, 51, 52] record.bidErrorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have offerErrorCode := readOptional_part [57, 57, 51, 53] record.offerErrorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have buyRevisionIndicator := readOptional_part [50, 49, 48, 48, 56] record.buyRevisionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have sellRevisionIndicator := readOptional_part [50, 49, 48, 48, 57] record.sellRevisionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  simp only [MassQuoteAck.decode, clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteID, quoteStatus, accountCode, lPRole, clearingInstructi, account, technicalOrdType, postingAction, ackQualifiers, quoteSetID, totNoQuotEntries, noQuoteEntries, quoteEntryID, bidQuoteID, offerQuoteID, securityID, securityIDSource, eMM, bidErrorCode, offerErrorCode, buyRevisionIndicator, sellRevisionIndicator, some_bind] <;> rfl

structure OrderCancelReject where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  clOrdID : Option (Terminated 1)  -- tag 11
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  orderID : Option (Terminated 1)  -- tag 37
  errorCode : Option (Terminated 1)  -- tag 9955
  cxlRejResponseTo : Terminated 1  -- tag 434
  collarRejType : Option (Terminated 1)  -- tag 9962
  breachedCollarPrice : Option (Terminated 1)  -- tag 21001
  ordStatus : Terminated 1  -- tag 39
  ackQualifiers : Option (Terminated 1)  -- tag 21014
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  oEPartitionID : Option (Terminated 1)  -- tag 21019

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [51, 55] record.orderID,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [57, 57, 54, 50] record.collarRejType,
   Part.optional [50, 49, 48, 48, 49] record.breachedCollarPrice,
   Part.required [51, 57] record.ordStatus,
   Part.optional [50, 49, 48, 49, 52] record.ackQualifiers,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55]], [[57, 57, 53, 53]], [[52, 51, 52]], [[57, 57, 54, 50]], [[50, 49, 48, 48, 49]], [[51, 57]], [[50, 49, 48, 49, 52]], [[50, 49, 48, 50, 49]], [[50, 49, 48, 49, 57]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let orderID ← readOptional [51, 55] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let collarRejType ← readOptional [57, 57, 54, 50] tokens
  let breachedCollarPrice ← readOptional [50, 49, 48, 48, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ackQualifiers ← readOptional [50, 49, 48, 49, 52] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  pure { clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, securityID, securityIDSource, eMM, orderID, errorCode, cxlRejResponseTo, collarRejType, breachedCollarPrice, ordStatus, ackQualifiers, logicalAccessID, oEPartitionID }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have collarRejType := readOptional_part [57, 57, 54, 50] record.collarRejType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have breachedCollarPrice := readOptional_part [50, 49, 48, 48, 49] record.breachedCollarPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have ackQualifiers := readOptional_part [50, 49, 48, 49, 52] record.ackQualifiers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, securityID, securityIDSource, eMM, orderID, errorCode, cxlRejResponseTo, collarRejType, breachedCollarPrice, ordStatus, ackQualifiers, logicalAccessID, oEPartitionID, some_bind] <;> rfl

structure RequestAckMessage where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  requestID : Option (Terminated 1)  -- tag 21060
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Terminated 1  -- tag 20020
  refMsgType : Option (Terminated 1)  -- tag 372
  errorCode : Option (Terminated 1)  -- tag 9955
  lPActionCode : Option (Terminated 1)  -- tag 10076

def RequestAckMessage.parts (record : RequestAckMessage) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [50, 49, 48, 54, 48] record.requestID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.optional [49, 48, 48, 55, 54] record.lPActionCode]

def RequestAckMessage.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[50, 49, 48, 54, 48]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 55, 50]], [[57, 57, 53, 53]], [[49, 48, 48, 55, 54]]]

theorem RequestAckMessage.shape (record : RequestAckMessage) : record.parts.map Part.tags = RequestAckMessage.tags := rfl

def RequestAckMessage.decode (tokens : List Token) : Option RequestAckMessage := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let requestID ← readOptional [50, 49, 48, 54, 48] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let lPActionCode ← readOptional [49, 48, 48, 55, 54] tokens
  pure { clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, requestID, securityID, securityIDSource, eMM, refMsgType, errorCode, lPActionCode }

theorem RequestAckMessage.decode_agrees (record : RequestAckMessage) (tokens : List Token)
    (agrees : ∀ tags ∈ RequestAckMessage.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RequestAckMessage.decode tokens = some record := by
  have distinct : RequestAckMessage.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have requestID := readOptional_part [50, 49, 48, 54, 48] record.requestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lPActionCode := readOptional_part [49, 48, 48, 55, 54] record.lPActionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [RequestAckMessage.decode, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, requestID, securityID, securityIDSource, eMM, refMsgType, errorCode, lPActionCode, some_bind] <;> rfl

structure OwnershipRequestAck where
  clOrdID : Terminated 1  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  oEPartitionID : Option (Terminated 1)  -- tag 21019
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  totalAffectedOrders : Terminated 1  -- tag 533
  orderCategory : Option (Terminated 1)  -- tag 21041

def OwnershipRequestAck.parts (record : OwnershipRequestAck) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [51, 55] record.orderID,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.required [53, 51, 51] record.totalAffectedOrders,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory]

def OwnershipRequestAck.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 56]], [[50, 50]], [[51, 55]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[53, 51, 51]], [[50, 49, 48, 52, 49]]]

theorem OwnershipRequestAck.shape (record : OwnershipRequestAck) : record.parts.map Part.tags = OwnershipRequestAck.tags := rfl

def OwnershipRequestAck.decode (tokens : List Token) : Option OwnershipRequestAck := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let totalAffectedOrders ← readRequired [53, 51, 51] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  pure { clOrdID, securityID, securityIDSource, orderID, oEPartitionID, logicalAccessID, totalAffectedOrders, orderCategory }

theorem OwnershipRequestAck.decode_agrees (record : OwnershipRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ OwnershipRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OwnershipRequestAck.decode tokens = some record := by
  have distinct : OwnershipRequestAck.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have totalAffectedOrders := readRequired_part [53, 51, 51] record.totalAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OwnershipRequestAck.decode, clOrdID, securityID, securityIDSource, orderID, oEPartitionID, logicalAccessID, totalAffectedOrders, orderCategory, some_bind] <;> rfl

structure QuoteRequestReject where
  oEGINFromMember : Terminated 1  -- tag 5979
  oEGOUTToME : Terminated 1  -- tag 7764
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Terminated 1  -- tag 21003
  oEGINFromME : Terminated 1  -- tag 7765
  quoteReqID : Terminated 1  -- tag 131
  quoteRequestRejectReason : Terminated 1  -- tag 658
  clOrdID : Terminated 1  -- tag 11
  text : Option (Terminated 1)  -- tag 58
  noRelatedSym : Terminated 1  -- tag 146
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [53, 57, 55, 57] record.oEGINFromMember,
   Part.required [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.required [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.required [55, 55, 54, 53] record.oEGINFromME,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.required [54, 53, 56] record.quoteRequestRejectReason,
   Part.required [49, 49] record.clOrdID,
   Part.optional [53, 56] record.text,
   Part.required [49, 52, 54] record.noRelatedSym,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[49, 51, 49]], [[54, 53, 56]], [[49, 49]], [[53, 56]], [[49, 52, 54]], [[52, 56]], [[50, 50]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let oEGINFromMember ← readRequired [53, 57, 55, 57] tokens
  let oEGOUTToME ← readRequired [55, 55, 54, 52] tokens
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readRequired [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readRequired [55, 55, 54, 53] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let quoteRequestRejectReason ← readRequired [54, 53, 56] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let text ← readOptional [53, 56] tokens
  let noRelatedSym ← readRequired [49, 52, 54] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  pure { oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, quoteReqID, quoteRequestRejectReason, clOrdID, text, noRelatedSym, securityID, securityIDSource }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have oEGINFromMember := readRequired_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGOUTToME := readRequired_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookOUTTime := readRequired_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readRequired_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteRequestRejectReason := readRequired_part [54, 53, 56] record.quoteRequestRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noRelatedSym := readRequired_part [49, 52, 54] record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, quoteReqID, quoteRequestRejectReason, clOrdID, text, noRelatedSym, securityID, securityIDSource, some_bind] <;> rfl

structure AskForQuote where
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  aFQReason : Terminated 1  -- tag 9939

def AskForQuote.parts (record : AskForQuote) : List Part :=
  [Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [57, 57, 51, 57] record.aFQReason]

def AskForQuote.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[57, 57, 51, 57]]]

theorem AskForQuote.shape (record : AskForQuote) : record.parts.map Part.tags = AskForQuote.tags := rfl

def AskForQuote.decode (tokens : List Token) : Option AskForQuote := do
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let aFQReason ← readRequired [57, 57, 51, 57] tokens
  pure { securityID, securityIDSource, eMM, aFQReason }

theorem AskForQuote.decode_agrees (record : AskForQuote) (tokens : List Token)
    (agrees : ∀ tags ∈ AskForQuote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AskForQuote.decode tokens = some record := by
  have distinct : AskForQuote.tags.flatten.Nodup := by decide +kernel
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have aFQReason := readRequired_part [57, 57, 51, 57] record.aFQReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [AskForQuote.decode, securityID, securityIDSource, eMM, aFQReason, some_bind] <;> rfl

structure UserNotification where
  userStatus : Terminated 1  -- tag 926
  noPartyIDs : Option (Terminated 1)  -- tag 453
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  partyRoleQualifi : Option (Terminated 1)  -- tag 2376
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  text : Option (Terminated 1)  -- tag 58
  riskFamily : Option (Terminated 1)  -- tag 20165
  marketCondition : Option (Terminated 1)  -- tag 21823
  noInstrumentScopes : Option (Terminated 1)  -- tag 1656
  instrumentScopeSecurityID : Option (Terminated 1)  -- tag 1538
  instrumentScopeSecurityIDSource : Option (Terminated 1)  -- tag 1539
  orderSizeLimit : Option (Terminated 1)  -- tag 21102
  orderAmountLimit : Option (Terminated 1)  -- tag 21809
  exposureSide : Option (Terminated 1)  -- tag 21818
  eMM : Option (Terminated 1)  -- tag 20020
  marketPlace : Option (Terminated 1)  -- tag 21825

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.required [57, 50, 54] record.userStatus,
   Part.optional [52, 53, 51] record.noPartyIDs,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifi,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 49, 54, 53] record.riskFamily,
   Part.optional [50, 49, 56, 50, 51] record.marketCondition,
   Part.optional [49, 54, 53, 54] record.noInstrumentScopes,
   Part.optional [49, 53, 51, 56] record.instrumentScopeSecurityID,
   Part.optional [49, 53, 51, 57] record.instrumentScopeSecurityIDSource,
   Part.optional [50, 49, 49, 48, 50] record.orderSizeLimit,
   Part.optional [50, 49, 56, 48, 57] record.orderAmountLimit,
   Part.optional [50, 49, 56, 49, 56] record.exposureSide,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 56, 50, 53] record.marketPlace]

def UserNotification.tags : List (List (List UInt8)) :=
  [[[57, 50, 54]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[50, 49, 48, 50, 49]], [[53, 56]], [[50, 48, 49, 54, 53]], [[50, 49, 56, 50, 51]], [[49, 54, 53, 54]], [[49, 53, 51, 56]], [[49, 53, 51, 57]], [[50, 49, 49, 48, 50]], [[50, 49, 56, 48, 57]], [[50, 49, 56, 49, 56]], [[50, 48, 48, 50, 48]], [[50, 49, 56, 50, 53]]]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let userStatus ← readRequired [57, 50, 54] tokens
  let noPartyIDs ← readOptional [52, 53, 51] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let partyRoleQualifi ← readOptional [50, 51, 55, 54] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let text ← readOptional [53, 56] tokens
  let riskFamily ← readOptional [50, 48, 49, 54, 53] tokens
  let marketCondition ← readOptional [50, 49, 56, 50, 51] tokens
  let noInstrumentScopes ← readOptional [49, 54, 53, 54] tokens
  let instrumentScopeSecurityID ← readOptional [49, 53, 51, 56] tokens
  let instrumentScopeSecurityIDSource ← readOptional [49, 53, 51, 57] tokens
  let orderSizeLimit ← readOptional [50, 49, 49, 48, 50] tokens
  let orderAmountLimit ← readOptional [50, 49, 56, 48, 57] tokens
  let exposureSide ← readOptional [50, 49, 56, 49, 56] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let marketPlace ← readOptional [50, 49, 56, 50, 53] tokens
  pure { userStatus, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, logicalAccessID, text, riskFamily, marketCondition, noInstrumentScopes, instrumentScopeSecurityID, instrumentScopeSecurityIDSource, orderSizeLimit, orderAmountLimit, exposureSide, eMM, marketPlace }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyRoleQualifi := readOptional_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have riskFamily := readOptional_part [50, 48, 49, 54, 53] record.riskFamily tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have marketCondition := readOptional_part [50, 49, 56, 50, 51] record.marketCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noInstrumentScopes := readOptional_part [49, 54, 53, 54] record.noInstrumentScopes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have instrumentScopeSecurityID := readOptional_part [49, 53, 51, 56] record.instrumentScopeSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have instrumentScopeSecurityIDSource := readOptional_part [49, 53, 51, 57] record.instrumentScopeSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderSizeLimit := readOptional_part [50, 49, 49, 48, 50] record.orderSizeLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderAmountLimit := readOptional_part [50, 49, 56, 48, 57] record.orderAmountLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have exposureSide := readOptional_part [50, 49, 56, 49, 56] record.exposureSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have marketPlace := readOptional_part [50, 49, 56, 50, 53] record.marketPlace tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [UserNotification.decode, userStatus, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, logicalAccessID, text, riskFamily, marketCondition, noInstrumentScopes, instrumentScopeSecurityID, instrumentScopeSecurityIDSource, orderSizeLimit, orderAmountLimit, exposureSide, eMM, marketPlace, some_bind] <;> rfl

structure OrderMassCancelReport where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Terminated 1  -- tag 21003
  oEGINFromME : Terminated 1  -- tag 7765
  clOrdID : Terminated 1  -- tag 11
  totalAffectedOrders : Terminated 1  -- tag 533
  classID : Option (Terminated 1)  -- tag 9945
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  side : Option (Terminated 1)  -- tag 54
  oEPartitionID : Option (Terminated 1)  -- tag 21019
  logicalAccessID : Option (Terminated 1)  -- tag 21021
  accountCode : Option (Terminated 1)  -- tag 6399
  massActionReportID : Terminated 1  -- tag 1369
  massCancelRequestType : Terminated 1  -- tag 530
  massCancelResponse : Terminated 1  -- tag 531
  orderCategory : Option (Terminated 1)  -- tag 21041
  ackQualifiers : Option (Terminated 1)  -- tag 21014
  targetPartyID : Option (Terminated 1)  -- tag 21095
  noPartyIDs : Terminated 1  -- tag 453
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifi : Terminated 1  -- tag 2376

def OrderMassCancelReport.parts (record : OrderMassCancelReport) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.required [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.required [55, 55, 54, 53] record.oEGINFromME,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 51] record.totalAffectedOrders,
   Part.optional [57, 57, 52, 53] record.classID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [53, 52] record.side,
   Part.optional [50, 49, 48, 49, 57] record.oEPartitionID,
   Part.optional [50, 49, 48, 50, 49] record.logicalAccessID,
   Part.optional [54, 51, 57, 57] record.accountCode,
   Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.required [53, 51, 49] record.massCancelResponse,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory,
   Part.optional [50, 49, 48, 49, 52] record.ackQualifiers,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.required [52, 53, 51] record.noPartyIDs,
   Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.required [50, 51, 55, 54] record.partyRoleQualifi]

def OrderMassCancelReport.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[49, 49]], [[53, 51, 51]], [[57, 57, 52, 53]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[53, 52]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 49]], [[54, 51, 57, 57]], [[49, 51, 54, 57]], [[53, 51, 48]], [[53, 51, 49]], [[50, 49, 48, 52, 49]], [[50, 49, 48, 49, 52]], [[50, 49, 48, 57, 53]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem OrderMassCancelReport.shape (record : OrderMassCancelReport) : record.parts.map Part.tags = OrderMassCancelReport.tags := rfl

def OrderMassCancelReport.decode (tokens : List Token) : Option OrderMassCancelReport := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readRequired [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readRequired [55, 55, 54, 53] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let totalAffectedOrders ← readRequired [53, 51, 51] tokens
  let classID ← readOptional [57, 57, 52, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let side ← readOptional [53, 52] tokens
  let oEPartitionID ← readOptional [50, 49, 48, 49, 57] tokens
  let logicalAccessID ← readOptional [50, 49, 48, 50, 49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let massCancelResponse ← readRequired [53, 51, 49] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  let ackQualifiers ← readOptional [50, 49, 48, 49, 52] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let noPartyIDs ← readRequired [52, 53, 51] tokens
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifi ← readRequired [50, 51, 55, 54] tokens
  pure { clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, totalAffectedOrders, classID, securityID, securityIDSource, eMM, side, oEPartitionID, logicalAccessID, accountCode, massActionReportID, massCancelRequestType, massCancelResponse, orderCategory, ackQualifiers, targetPartyID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi }

theorem OrderMassCancelReport.decode_agrees (record : OrderMassCancelReport) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReport.decode tokens = some record := by
  have distinct : OrderMassCancelReport.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bookOUTTime := readRequired_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGINFromME := readRequired_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have totalAffectedOrders := readRequired_part [53, 51, 51] record.totalAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have classID := readOptional_part [57, 57, 52, 53] record.classID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have oEPartitionID := readOptional_part [50, 49, 48, 49, 57] record.oEPartitionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have logicalAccessID := readOptional_part [50, 49, 48, 50, 49] record.logicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have massCancelResponse := readRequired_part [53, 51, 49] record.massCancelResponse tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have ackQualifiers := readOptional_part [50, 49, 48, 49, 52] record.ackQualifiers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  simp only [OrderMassCancelReport.decode, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, clOrdID, totalAffectedOrders, classID, securityID, securityIDSource, eMM, side, oEPartitionID, logicalAccessID, accountCode, massActionReportID, massCancelRequestType, massCancelResponse, orderCategory, ackQualifiers, targetPartyID, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, some_bind] <;> rfl

structure RFQNotification where
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  quoteReqID : Terminated 1  -- tag 131
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  orderQty : Terminated 1  -- tag 38
  side : Option (Terminated 1)  -- tag 54
  darkExecutionInstruction : Terminated 1  -- tag 20052
  minQty : Option (Terminated 1)  -- tag 110
  orderCategory : Option (Terminated 1)  -- tag 21041
  accountCode : Option (Terminated 1)  -- tag 6399

def RFQNotification.parts (record : RFQNotification) : List Part :=
  [Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [51, 56] record.orderQty,
   Part.optional [53, 52] record.side,
   Part.required [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 48, 52, 49] record.orderCategory,
   Part.optional [54, 51, 57, 57] record.accountCode]

def RFQNotification.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[49, 51, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[51, 56]], [[53, 52]], [[50, 48, 48, 53, 50]], [[49, 49, 48]], [[50, 49, 48, 52, 49]], [[54, 51, 57, 57]]]

theorem RFQNotification.shape (record : RFQNotification) : record.parts.map Part.tags = RFQNotification.tags := rfl

def RFQNotification.decode (tokens : List Token) : Option RFQNotification := do
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let side ← readOptional [53, 52] tokens
  let darkExecutionInstruction ← readRequired [50, 48, 48, 53, 50] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let orderCategory ← readOptional [50, 49, 48, 52, 49] tokens
  let accountCode ← readOptional [54, 51, 57, 57] tokens
  pure { bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteReqID, securityID, securityIDSource, eMM, orderQty, side, darkExecutionInstruction, minQty, orderCategory, accountCode }

theorem RFQNotification.decode_agrees (record : RFQNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ RFQNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RFQNotification.decode tokens = some record := by
  have distinct : RFQNotification.tags.flatten.Nodup := by decide +kernel
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have darkExecutionInstruction := readRequired_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderCategory := readOptional_part [50, 49, 48, 52, 49] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [RFQNotification.decode, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteReqID, securityID, securityIDSource, eMM, orderQty, side, darkExecutionInstruction, minQty, orderCategory, accountCode, some_bind] <;> rfl

structure RFQMatchingStatus where
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  quoteReqID : Terminated 1  -- tag 131
  potentialMatchingPrice : Option (Terminated 1)  -- tag 21030
  potentialMatchingQuantity : Terminated 1  -- tag 21031
  side : Terminated 1  -- tag 54
  numberOfLPs : Option (Terminated 1)  -- tag 21034

def RFQMatchingStatus.parts (record : RFQMatchingStatus) : List Part :=
  [Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [50, 49, 48, 51, 48] record.potentialMatchingPrice,
   Part.required [50, 49, 48, 51, 49] record.potentialMatchingQuantity,
   Part.required [53, 52] record.side,
   Part.optional [50, 49, 48, 51, 52] record.numberOfLPs]

def RFQMatchingStatus.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[49, 51, 49]], [[50, 49, 48, 51, 48]], [[50, 49, 48, 51, 49]], [[53, 52]], [[50, 49, 48, 51, 52]]]

theorem RFQMatchingStatus.shape (record : RFQMatchingStatus) : record.parts.map Part.tags = RFQMatchingStatus.tags := rfl

def RFQMatchingStatus.decode (tokens : List Token) : Option RFQMatchingStatus := do
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let potentialMatchingPrice ← readOptional [50, 49, 48, 51, 48] tokens
  let potentialMatchingQuantity ← readRequired [50, 49, 48, 51, 49] tokens
  let side ← readRequired [53, 52] tokens
  let numberOfLPs ← readOptional [50, 49, 48, 51, 52] tokens
  pure { bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, securityID, securityIDSource, eMM, quoteReqID, potentialMatchingPrice, potentialMatchingQuantity, side, numberOfLPs }

theorem RFQMatchingStatus.decode_agrees (record : RFQMatchingStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ RFQMatchingStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RFQMatchingStatus.decode tokens = some record := by
  have distinct : RFQMatchingStatus.tags.flatten.Nodup := by decide +kernel
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have potentialMatchingPrice := readOptional_part [50, 49, 48, 51, 48] record.potentialMatchingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have potentialMatchingQuantity := readRequired_part [50, 49, 48, 51, 49] record.potentialMatchingQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have numberOfLPs := readOptional_part [50, 49, 48, 51, 52] record.numberOfLPs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [RFQMatchingStatus.decode, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, securityID, securityIDSource, eMM, quoteReqID, potentialMatchingPrice, potentialMatchingQuantity, side, numberOfLPs, some_bind] <;> rfl

structure RFQLPMatchingStatus where
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  quoteReqID : Terminated 1  -- tag 131
  potentialMatchingQuantity : Terminated 1  -- tag 21031
  side : Terminated 1  -- tag 54

def RFQLPMatchingStatus.parts (record : RFQLPMatchingStatus) : List Part :=
  [Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.required [50, 49, 48, 51, 49] record.potentialMatchingQuantity,
   Part.required [53, 52] record.side]

def RFQLPMatchingStatus.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[49, 51, 49]], [[50, 49, 48, 51, 49]], [[53, 52]]]

theorem RFQLPMatchingStatus.shape (record : RFQLPMatchingStatus) : record.parts.map Part.tags = RFQLPMatchingStatus.tags := rfl

def RFQLPMatchingStatus.decode (tokens : List Token) : Option RFQLPMatchingStatus := do
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let potentialMatchingQuantity ← readRequired [50, 49, 48, 51, 49] tokens
  let side ← readRequired [53, 52] tokens
  pure { bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, securityID, securityIDSource, eMM, quoteReqID, potentialMatchingQuantity, side }

theorem RFQLPMatchingStatus.decode_agrees (record : RFQLPMatchingStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ RFQLPMatchingStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RFQLPMatchingStatus.decode tokens = some record := by
  have distinct : RFQLPMatchingStatus.tags.flatten.Nodup := by decide +kernel
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have potentialMatchingQuantity := readRequired_part [50, 49, 48, 51, 49] record.potentialMatchingQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [RFQLPMatchingStatus.decode, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, securityID, securityIDSource, eMM, quoteReqID, potentialMatchingQuantity, side, some_bind] <;> rfl

structure RequestForExecution where
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020

def RequestForExecution.parts (record : RequestForExecution) : List Part :=
  [Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM]

def RequestForExecution.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]]]

theorem RequestForExecution.shape (record : RequestForExecution) : record.parts.map Part.tags = RequestForExecution.tags := rfl

def RequestForExecution.decode (tokens : List Token) : Option RequestForExecution := do
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  pure { securityID, securityIDSource, eMM }

theorem RequestForExecution.decode_agrees (record : RequestForExecution) (tokens : List Token)
    (agrees : ∀ tags ∈ RequestForExecution.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RequestForExecution.decode tokens = some record := by
  have distinct : RequestForExecution.tags.flatten.Nodup := by decide +kernel
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [RequestForExecution.decode, securityID, securityIDSource, eMM, some_bind] <;> rfl

structure SecurityDefinition where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  securityReqID : Terminated 1  -- tag 320
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  errorCode : Option (Terminated 1)  -- tag 9955

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.required [51, 50, 48] record.securityReqID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [57, 57, 53, 53] record.errorCode]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[55, 55, 54, 52]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[51, 50, 48]], [[52, 56]], [[50, 50]], [[57, 57, 53, 53]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  pure { clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, securityReqID, securityID, securityIDSource, errorCode }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [SecurityDefinition.decode, clientMessageSendingTime, oEGINFromMember, oEGOUTToME, bookINTime, bookOUTTime, oEGINFromME, securityReqID, securityID, securityIDSource, errorCode, some_bind] <;> rfl

structure WholesaleOrderAck where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  clOrdID : Option (Terminated 1)  -- tag 11
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  wholesaleTradeType : Terminated 1  -- tag 21083
  tradePublicationType : Option (Terminated 1)  -- tag 1390
  lISTransactionID : Option (Terminated 1)  -- tag 21085
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  price : Option (Terminated 1)  -- tag 44
  quantity : Option (Terminated 1)  -- tag 53
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
  ackStatus : Terminated 1  -- tag 5711
  ackQualifiers : Terminated 1  -- tag 21014
  errorCode : Option (Terminated 1)  -- tag 9955
  noLegs : Terminated 1  -- tag 555
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Terminated 1  -- tag 602
  legSecurityIDSo : Terminated 1  -- tag 603
  bidQuoteID : Option (Terminated 1)  -- tag 1747
  offerQuoteID : Option (Terminated 1)  -- tag 1748
  bidNonExecClID : Option (Terminated 1)  -- tag 21089
  offerNonExecClID : Option (Terminated 1)  -- tag 21090
  legSide : Option (Terminated 1)  -- tag 624
  legErrorCode : Option (Terminated 1)  -- tag 2108
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  noNestedOrderAttributes : Option (Terminated 1)  -- tag 21086

def WholesaleOrderAck.parts (record : WholesaleOrderAck) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [49, 49] record.clOrdID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 49, 48, 56, 51] record.wholesaleTradeType,
   Part.optional [49, 51, 57, 48] record.tradePublicationType,
   Part.optional [50, 49, 48, 56, 53] record.lISTransactionID,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 51] record.quantity,
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
   Part.required [53, 55, 49, 49] record.ackStatus,
   Part.required [50, 49, 48, 49, 52] record.ackQualifiers,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 50] record.legSecurityID,
   Part.required [54, 48, 51] record.legSecurityIDSo,
   Part.optional [49, 55, 52, 55] record.bidQuoteID,
   Part.optional [49, 55, 52, 56] record.offerQuoteID,
   Part.optional [50, 49, 48, 56, 57] record.bidNonExecClID,
   Part.optional [50, 49, 48, 57, 48] record.offerNonExecClID,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [50, 49, 48, 56] record.legErrorCode,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [50, 49, 48, 56, 54] record.noNestedOrderAttributes]

def WholesaleOrderAck.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[49, 49]], [[52, 56]], [[50, 50]], [[50, 49, 48, 56, 51]], [[49, 51, 57, 48]], [[50, 49, 48, 56, 53]], [[49, 54, 55]], [[55, 54, 50]], [[52, 52]], [[53, 51]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[49, 55, 50, 52]], [[50, 53, 57, 51]], [[50, 53, 57, 52]], [[50, 53, 57, 53]], [[50, 49, 48, 56, 50]], [[50, 49, 48, 57, 54]], [[53, 55, 49, 49]], [[50, 49, 48, 49, 52]], [[57, 57, 53, 53]], [[53, 53, 53]], [[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[49, 55, 52, 55]], [[49, 55, 52, 56]], [[50, 49, 48, 56, 57]], [[50, 49, 48, 57, 48]], [[54, 50, 52]], [[50, 49, 48, 56]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[50, 49, 48, 56, 54]]]

theorem WholesaleOrderAck.shape (record : WholesaleOrderAck) : record.parts.map Part.tags = WholesaleOrderAck.tags := rfl

def WholesaleOrderAck.decode (tokens : List Token) : Option WholesaleOrderAck := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let wholesaleTradeType ← readRequired [50, 49, 48, 56, 51] tokens
  let tradePublicationType ← readOptional [49, 51, 57, 48] tokens
  let lISTransactionID ← readOptional [50, 49, 48, 56, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let price ← readOptional [52, 52] tokens
  let quantity ← readOptional [53, 51] tokens
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
  let ackStatus ← readRequired [53, 55, 49, 49] tokens
  let ackQualifiers ← readRequired [50, 49, 48, 49, 52] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readRequired [54, 48, 50] tokens
  let legSecurityIDSo ← readRequired [54, 48, 51] tokens
  let bidQuoteID ← readOptional [49, 55, 52, 55] tokens
  let offerQuoteID ← readOptional [49, 55, 52, 56] tokens
  let bidNonExecClID ← readOptional [50, 49, 48, 56, 57] tokens
  let offerNonExecClID ← readOptional [50, 49, 48, 57, 48] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legErrorCode ← readOptional [50, 49, 48, 56] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let noNestedOrderAttributes ← readOptional [50, 49, 48, 56, 54] tokens
  pure { clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, clOrdID, securityID, securityIDSource, wholesaleTradeType, tradePublicationType, lISTransactionID, securityType, securitySubType, price, quantity, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, wholesaleSide, eSCBMembership, ackStatus, ackQualifiers, errorCode, noLegs, legSymbol, legSecurityID, legSecurityIDSo, bidQuoteID, offerQuoteID, bidNonExecClID, offerNonExecClID, legSide, legErrorCode, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noNestedOrderAttributes }

theorem WholesaleOrderAck.decode_agrees (record : WholesaleOrderAck) (tokens : List Token)
    (agrees : ∀ tags ∈ WholesaleOrderAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    WholesaleOrderAck.decode tokens = some record := by
  have distinct : WholesaleOrderAck.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have wholesaleTradeType := readRequired_part [50, 49, 48, 56, 51] record.wholesaleTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradePublicationType := readOptional_part [49, 51, 57, 48] record.tradePublicationType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lISTransactionID := readOptional_part [50, 49, 48, 56, 53] record.lISTransactionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have quantity := readOptional_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noPartyIDs := readRequired_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have partyRoleQualifi := readRequired_part [50, 51, 55, 54] record.partyRoleQualifi tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noOrderAttribut := readOptional_part [50, 53, 57, 51] record.noOrderAttribut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have orderAttributeTy := readOptional_part [50, 53, 57, 52] record.orderAttributeTy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have wholesaleSide := readRequired_part [50, 49, 48, 56, 50] record.wholesaleSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have eSCBMembership := readOptional_part [50, 49, 48, 57, 54] record.eSCBMembership tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have ackStatus := readRequired_part [53, 55, 49, 49] record.ackStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have ackQualifiers := readRequired_part [50, 49, 48, 49, 52] record.ackQualifiers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have legSecurityID := readRequired_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have legSecurityIDSo := readRequired_part [54, 48, 51] record.legSecurityIDSo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have bidQuoteID := readOptional_part [49, 55, 52, 55] record.bidQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have offerQuoteID := readOptional_part [49, 55, 52, 56] record.offerQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have bidNonExecClID := readOptional_part [50, 49, 48, 56, 57] record.bidNonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have offerNonExecClID := readOptional_part [50, 49, 48, 57, 48] record.offerNonExecClID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have legErrorCode := readOptional_part [50, 49, 48, 56] record.legErrorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have nestedPartyID := readOptional_part [53, 50, 52] record.nestedPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have nestedPartyIDSource := readOptional_part [53, 50, 53] record.nestedPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have nestedPartyRole := readOptional_part [53, 51, 56] record.nestedPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have nestedPartyRoleQualifier := readOptional_part [50, 51, 56, 52] record.nestedPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have noNestedOrderAttributes := readOptional_part [50, 49, 48, 56, 54] record.noNestedOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  simp only [WholesaleOrderAck.decode, clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, clOrdID, securityID, securityIDSource, wholesaleTradeType, tradePublicationType, lISTransactionID, securityType, securitySubType, price, quantity, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, orderOrigination, noOrderAttribut, orderAttributeTy, orderAttributeValue, wholesaleSide, eSCBMembership, ackStatus, ackQualifiers, errorCode, noLegs, legSymbol, legSecurityID, legSecurityIDSo, bidQuoteID, offerQuoteID, bidNonExecClID, offerNonExecClID, legSide, legErrorCode, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, noNestedOrderAttributes, some_bind] <;> rfl

structure ERGCommandAck where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  requestID : Terminated 1  -- tag 21060
  targetFirmID : Terminated 1  -- tag 21098
  targetPartyID : Option (Terminated 1)  -- tag 21095
  targetClientShortCode : Option (Terminated 1)  -- tag 21108
  targetLogicalAccessID : Option (Terminated 1)  -- tag 21099
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  purge : Option (Terminated 1)  -- tag 21100
  oSLFlag : Option (Terminated 1)  -- tag 21101
  orderSizeLimit : Option (Terminated 1)  -- tag 21102
  oALFlag : Option (Terminated 1)  -- tag 21808
  orderAmountLimit : Option (Terminated 1)  -- tag 21809
  ackStatus : Terminated 1  -- tag 5711
  errorCode : Option (Terminated 1)  -- tag 9955
  mEPFlag : Option (Terminated 1)  -- tag 21811
  maximumLongExposure : Option (Terminated 1)  -- tag 21812
  maximumShortExposure : Option (Terminated 1)  -- tag 21813
  mEPBreachAction : Option (Terminated 1)  -- tag 21814
  targetMarketPlaceID : Option (Terminated 1)  -- tag 21824
  noThresholds : Option (Terminated 1)  -- tag 21815
  thresholdValue : Option (Terminated 1)  -- tag 21817
  thresholdBreachAction : Option (Terminated 1)  -- tag 21816
  marketCondition : Option (Terminated 1)  -- tag 21823

def ERGCommandAck.parts (record : ERGCommandAck) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [50, 49, 48, 54, 48] record.requestID,
   Part.required [50, 49, 48, 57, 56] record.targetFirmID,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.optional [50, 49, 49, 48, 56] record.targetClientShortCode,
   Part.optional [50, 49, 48, 57, 57] record.targetLogicalAccessID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 49, 48, 48] record.purge,
   Part.optional [50, 49, 49, 48, 49] record.oSLFlag,
   Part.optional [50, 49, 49, 48, 50] record.orderSizeLimit,
   Part.optional [50, 49, 56, 48, 56] record.oALFlag,
   Part.optional [50, 49, 56, 48, 57] record.orderAmountLimit,
   Part.required [53, 55, 49, 49] record.ackStatus,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.optional [50, 49, 56, 49, 49] record.mEPFlag,
   Part.optional [50, 49, 56, 49, 50] record.maximumLongExposure,
   Part.optional [50, 49, 56, 49, 51] record.maximumShortExposure,
   Part.optional [50, 49, 56, 49, 52] record.mEPBreachAction,
   Part.optional [50, 49, 56, 50, 52] record.targetMarketPlaceID,
   Part.optional [50, 49, 56, 49, 53] record.noThresholds,
   Part.optional [50, 49, 56, 49, 55] record.thresholdValue,
   Part.optional [50, 49, 56, 49, 54] record.thresholdBreachAction,
   Part.optional [50, 49, 56, 50, 51] record.marketCondition]

def ERGCommandAck.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[50, 49, 48, 54, 48]], [[50, 49, 48, 57, 56]], [[50, 49, 48, 57, 53]], [[50, 49, 49, 48, 56]], [[50, 49, 48, 57, 57]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[50, 49, 49, 48, 48]], [[50, 49, 49, 48, 49]], [[50, 49, 49, 48, 50]], [[50, 49, 56, 48, 56]], [[50, 49, 56, 48, 57]], [[53, 55, 49, 49]], [[57, 57, 53, 53]], [[50, 49, 56, 49, 49]], [[50, 49, 56, 49, 50]], [[50, 49, 56, 49, 51]], [[50, 49, 56, 49, 52]], [[50, 49, 56, 50, 52]], [[50, 49, 56, 49, 53]], [[50, 49, 56, 49, 55]], [[50, 49, 56, 49, 54]], [[50, 49, 56, 50, 51]]]

theorem ERGCommandAck.shape (record : ERGCommandAck) : record.parts.map Part.tags = ERGCommandAck.tags := rfl

def ERGCommandAck.decode (tokens : List Token) : Option ERGCommandAck := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let requestID ← readRequired [50, 49, 48, 54, 48] tokens
  let targetFirmID ← readRequired [50, 49, 48, 57, 56] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let targetClientShortCode ← readOptional [50, 49, 49, 48, 56] tokens
  let targetLogicalAccessID ← readOptional [50, 49, 48, 57, 57] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let purge ← readOptional [50, 49, 49, 48, 48] tokens
  let oSLFlag ← readOptional [50, 49, 49, 48, 49] tokens
  let orderSizeLimit ← readOptional [50, 49, 49, 48, 50] tokens
  let oALFlag ← readOptional [50, 49, 56, 48, 56] tokens
  let orderAmountLimit ← readOptional [50, 49, 56, 48, 57] tokens
  let ackStatus ← readRequired [53, 55, 49, 49] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let mEPFlag ← readOptional [50, 49, 56, 49, 49] tokens
  let maximumLongExposure ← readOptional [50, 49, 56, 49, 50] tokens
  let maximumShortExposure ← readOptional [50, 49, 56, 49, 51] tokens
  let mEPBreachAction ← readOptional [50, 49, 56, 49, 52] tokens
  let targetMarketPlaceID ← readOptional [50, 49, 56, 50, 52] tokens
  let noThresholds ← readOptional [50, 49, 56, 49, 53] tokens
  let thresholdValue ← readOptional [50, 49, 56, 49, 55] tokens
  let thresholdBreachAction ← readOptional [50, 49, 56, 49, 54] tokens
  let marketCondition ← readOptional [50, 49, 56, 50, 51] tokens
  pure { clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, requestID, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, securityID, securityIDSource, eMM, purge, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, ackStatus, errorCode, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, targetMarketPlaceID, noThresholds, thresholdValue, thresholdBreachAction, marketCondition }

theorem ERGCommandAck.decode_agrees (record : ERGCommandAck) (tokens : List Token)
    (agrees : ∀ tags ∈ ERGCommandAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ERGCommandAck.decode tokens = some record := by
  have distinct : ERGCommandAck.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have requestID := readRequired_part [50, 49, 48, 54, 48] record.requestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have targetFirmID := readRequired_part [50, 49, 48, 57, 56] record.targetFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have targetClientShortCode := readOptional_part [50, 49, 49, 48, 56] record.targetClientShortCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have targetLogicalAccessID := readOptional_part [50, 49, 48, 57, 57] record.targetLogicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have purge := readOptional_part [50, 49, 49, 48, 48] record.purge tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have oSLFlag := readOptional_part [50, 49, 49, 48, 49] record.oSLFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderSizeLimit := readOptional_part [50, 49, 49, 48, 50] record.orderSizeLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have oALFlag := readOptional_part [50, 49, 56, 48, 56] record.oALFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have orderAmountLimit := readOptional_part [50, 49, 56, 48, 57] record.orderAmountLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have ackStatus := readRequired_part [53, 55, 49, 49] record.ackStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have mEPFlag := readOptional_part [50, 49, 56, 49, 49] record.mEPFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have maximumLongExposure := readOptional_part [50, 49, 56, 49, 50] record.maximumLongExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have maximumShortExposure := readOptional_part [50, 49, 56, 49, 51] record.maximumShortExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have mEPBreachAction := readOptional_part [50, 49, 56, 49, 52] record.mEPBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have targetMarketPlaceID := readOptional_part [50, 49, 56, 50, 52] record.targetMarketPlaceID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noThresholds := readOptional_part [50, 49, 56, 49, 53] record.noThresholds tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have thresholdValue := readOptional_part [50, 49, 56, 49, 55] record.thresholdValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have thresholdBreachAction := readOptional_part [50, 49, 56, 49, 54] record.thresholdBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have marketCondition := readOptional_part [50, 49, 56, 50, 51] record.marketCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  simp only [ERGCommandAck.decode, clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, requestID, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, securityID, securityIDSource, eMM, purge, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, ackStatus, errorCode, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, targetMarketPlaceID, noThresholds, thresholdValue, thresholdBreachAction, marketCondition, some_bind] <;> rfl

structure ERGMEPBreachAlert where
  targetFirmID : Terminated 1  -- tag 21098
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  exposureSide : Option (Terminated 1)  -- tag 21818
  positionLimit : Option (Terminated 1)  -- tag 21819
  currentExposure : Terminated 1  -- tag 21820
  mEPBreachAction : Option (Terminated 1)  -- tag 21814
  thresholdValue : Option (Terminated 1)  -- tag 21817
  thresholdBreachAction : Option (Terminated 1)  -- tag 21816
  isBlocked : Option (Terminated 1)  -- tag 21821
  targetLogicalAccessID : Option (Terminated 1)  -- tag 21099

def ERGMEPBreachAlert.parts (record : ERGMEPBreachAlert) : List Part :=
  [Part.required [50, 49, 48, 57, 56] record.targetFirmID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 49, 56, 49, 56] record.exposureSide,
   Part.optional [50, 49, 56, 49, 57] record.positionLimit,
   Part.required [50, 49, 56, 50, 48] record.currentExposure,
   Part.optional [50, 49, 56, 49, 52] record.mEPBreachAction,
   Part.optional [50, 49, 56, 49, 55] record.thresholdValue,
   Part.optional [50, 49, 56, 49, 54] record.thresholdBreachAction,
   Part.optional [50, 49, 56, 50, 49] record.isBlocked,
   Part.optional [50, 49, 48, 57, 57] record.targetLogicalAccessID]

def ERGMEPBreachAlert.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 57, 56]], [[52, 56]], [[50, 50]], [[50, 49, 56, 49, 56]], [[50, 49, 56, 49, 57]], [[50, 49, 56, 50, 48]], [[50, 49, 56, 49, 52]], [[50, 49, 56, 49, 55]], [[50, 49, 56, 49, 54]], [[50, 49, 56, 50, 49]], [[50, 49, 48, 57, 57]]]

theorem ERGMEPBreachAlert.shape (record : ERGMEPBreachAlert) : record.parts.map Part.tags = ERGMEPBreachAlert.tags := rfl

def ERGMEPBreachAlert.decode (tokens : List Token) : Option ERGMEPBreachAlert := do
  let targetFirmID ← readRequired [50, 49, 48, 57, 56] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let exposureSide ← readOptional [50, 49, 56, 49, 56] tokens
  let positionLimit ← readOptional [50, 49, 56, 49, 57] tokens
  let currentExposure ← readRequired [50, 49, 56, 50, 48] tokens
  let mEPBreachAction ← readOptional [50, 49, 56, 49, 52] tokens
  let thresholdValue ← readOptional [50, 49, 56, 49, 55] tokens
  let thresholdBreachAction ← readOptional [50, 49, 56, 49, 54] tokens
  let isBlocked ← readOptional [50, 49, 56, 50, 49] tokens
  let targetLogicalAccessID ← readOptional [50, 49, 48, 57, 57] tokens
  pure { targetFirmID, securityID, securityIDSource, exposureSide, positionLimit, currentExposure, mEPBreachAction, thresholdValue, thresholdBreachAction, isBlocked, targetLogicalAccessID }

theorem ERGMEPBreachAlert.decode_agrees (record : ERGMEPBreachAlert) (tokens : List Token)
    (agrees : ∀ tags ∈ ERGMEPBreachAlert.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ERGMEPBreachAlert.decode tokens = some record := by
  have distinct : ERGMEPBreachAlert.tags.flatten.Nodup := by decide +kernel
  have targetFirmID := readRequired_part [50, 49, 48, 57, 56] record.targetFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have exposureSide := readOptional_part [50, 49, 56, 49, 56] record.exposureSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have positionLimit := readOptional_part [50, 49, 56, 49, 57] record.positionLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currentExposure := readRequired_part [50, 49, 56, 50, 48] record.currentExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have mEPBreachAction := readOptional_part [50, 49, 56, 49, 52] record.mEPBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have thresholdValue := readOptional_part [50, 49, 56, 49, 55] record.thresholdValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have thresholdBreachAction := readOptional_part [50, 49, 56, 49, 54] record.thresholdBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have isBlocked := readOptional_part [50, 49, 56, 50, 49] record.isBlocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have targetLogicalAccessID := readOptional_part [50, 49, 48, 57, 57] record.targetLogicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ERGMEPBreachAlert.decode, targetFirmID, securityID, securityIDSource, exposureSide, positionLimit, currentExposure, mEPBreachAction, thresholdValue, thresholdBreachAction, isBlocked, targetLogicalAccessID, some_bind] <;> rfl

structure RiskControlDetails where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  requestID : Terminated 1  -- tag 21060
  ackStatus : Terminated 1  -- tag 5711
  errorCode : Option (Terminated 1)  -- tag 9955
  riskControlType : Terminated 1  -- tag 21103
  noParameters : Option (Terminated 1)  -- tag 21107
  targetFirmID : Option (Terminated 1)  -- tag 21098
  targetPartyID : Option (Terminated 1)  -- tag 21095
  targetClientShortCode : Option (Terminated 1)  -- tag 21108
  targetLogicalAccessID : Option (Terminated 1)  -- tag 21099
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  eRGStatus : Option (Terminated 1)  -- tag 21105
  oSLFlag : Option (Terminated 1)  -- tag 21101
  orderSizeLimit : Option (Terminated 1)  -- tag 21102
  oALFlag : Option (Terminated 1)  -- tag 21808
  orderAmountLimit : Option (Terminated 1)  -- tag 21809
  mEPFlag : Option (Terminated 1)  -- tag 21811
  maximumLongExposure : Option (Terminated 1)  -- tag 21812
  maximumShortExposure : Option (Terminated 1)  -- tag 21813
  mEPBreachAction : Option (Terminated 1)  -- tag 21814
  marketCondition : Option (Terminated 1)  -- tag 21823
  targetMarketPlaceID : Option (Terminated 1)  -- tag 21824
  noThresholds : Option (Terminated 1)  -- tag 21815
  thresholdValue : Option (Terminated 1)  -- tag 21817
  thresholdBreachAction : Option (Terminated 1)  -- tag 21816

def RiskControlDetails.parts (record : RiskControlDetails) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [50, 49, 48, 54, 48] record.requestID,
   Part.required [53, 55, 49, 49] record.ackStatus,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.required [50, 49, 49, 48, 51] record.riskControlType,
   Part.optional [50, 49, 49, 48, 55] record.noParameters,
   Part.optional [50, 49, 48, 57, 56] record.targetFirmID,
   Part.optional [50, 49, 48, 57, 53] record.targetPartyID,
   Part.optional [50, 49, 49, 48, 56] record.targetClientShortCode,
   Part.optional [50, 49, 48, 57, 57] record.targetLogicalAccessID,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 49, 48, 53] record.eRGStatus,
   Part.optional [50, 49, 49, 48, 49] record.oSLFlag,
   Part.optional [50, 49, 49, 48, 50] record.orderSizeLimit,
   Part.optional [50, 49, 56, 48, 56] record.oALFlag,
   Part.optional [50, 49, 56, 48, 57] record.orderAmountLimit,
   Part.optional [50, 49, 56, 49, 49] record.mEPFlag,
   Part.optional [50, 49, 56, 49, 50] record.maximumLongExposure,
   Part.optional [50, 49, 56, 49, 51] record.maximumShortExposure,
   Part.optional [50, 49, 56, 49, 52] record.mEPBreachAction,
   Part.optional [50, 49, 56, 50, 51] record.marketCondition,
   Part.optional [50, 49, 56, 50, 52] record.targetMarketPlaceID,
   Part.optional [50, 49, 56, 49, 53] record.noThresholds,
   Part.optional [50, 49, 56, 49, 55] record.thresholdValue,
   Part.optional [50, 49, 56, 49, 54] record.thresholdBreachAction]

def RiskControlDetails.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[53, 57, 55, 57]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[50, 49, 48, 54, 48]], [[53, 55, 49, 49]], [[57, 57, 53, 53]], [[50, 49, 49, 48, 51]], [[50, 49, 49, 48, 55]], [[50, 49, 48, 57, 56]], [[50, 49, 48, 57, 53]], [[50, 49, 49, 48, 56]], [[50, 49, 48, 57, 57]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[50, 49, 49, 48, 53]], [[50, 49, 49, 48, 49]], [[50, 49, 49, 48, 50]], [[50, 49, 56, 48, 56]], [[50, 49, 56, 48, 57]], [[50, 49, 56, 49, 49]], [[50, 49, 56, 49, 50]], [[50, 49, 56, 49, 51]], [[50, 49, 56, 49, 52]], [[50, 49, 56, 50, 51]], [[50, 49, 56, 50, 52]], [[50, 49, 56, 49, 53]], [[50, 49, 56, 49, 55]], [[50, 49, 56, 49, 54]]]

theorem RiskControlDetails.shape (record : RiskControlDetails) : record.parts.map Part.tags = RiskControlDetails.tags := rfl

def RiskControlDetails.decode (tokens : List Token) : Option RiskControlDetails := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let requestID ← readRequired [50, 49, 48, 54, 48] tokens
  let ackStatus ← readRequired [53, 55, 49, 49] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let riskControlType ← readRequired [50, 49, 49, 48, 51] tokens
  let noParameters ← readOptional [50, 49, 49, 48, 55] tokens
  let targetFirmID ← readOptional [50, 49, 48, 57, 56] tokens
  let targetPartyID ← readOptional [50, 49, 48, 57, 53] tokens
  let targetClientShortCode ← readOptional [50, 49, 49, 48, 56] tokens
  let targetLogicalAccessID ← readOptional [50, 49, 48, 57, 57] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let eRGStatus ← readOptional [50, 49, 49, 48, 53] tokens
  let oSLFlag ← readOptional [50, 49, 49, 48, 49] tokens
  let orderSizeLimit ← readOptional [50, 49, 49, 48, 50] tokens
  let oALFlag ← readOptional [50, 49, 56, 48, 56] tokens
  let orderAmountLimit ← readOptional [50, 49, 56, 48, 57] tokens
  let mEPFlag ← readOptional [50, 49, 56, 49, 49] tokens
  let maximumLongExposure ← readOptional [50, 49, 56, 49, 50] tokens
  let maximumShortExposure ← readOptional [50, 49, 56, 49, 51] tokens
  let mEPBreachAction ← readOptional [50, 49, 56, 49, 52] tokens
  let marketCondition ← readOptional [50, 49, 56, 50, 51] tokens
  let targetMarketPlaceID ← readOptional [50, 49, 56, 50, 52] tokens
  let noThresholds ← readOptional [50, 49, 56, 49, 53] tokens
  let thresholdValue ← readOptional [50, 49, 56, 49, 55] tokens
  let thresholdBreachAction ← readOptional [50, 49, 56, 49, 54] tokens
  pure { clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, requestID, ackStatus, errorCode, riskControlType, noParameters, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, securityID, securityIDSource, eMM, eRGStatus, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, marketCondition, targetMarketPlaceID, noThresholds, thresholdValue, thresholdBreachAction }

theorem RiskControlDetails.decode_agrees (record : RiskControlDetails) (tokens : List Token)
    (agrees : ∀ tags ∈ RiskControlDetails.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RiskControlDetails.decode tokens = some record := by
  have distinct : RiskControlDetails.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have requestID := readRequired_part [50, 49, 48, 54, 48] record.requestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ackStatus := readRequired_part [53, 55, 49, 49] record.ackStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have riskControlType := readRequired_part [50, 49, 49, 48, 51] record.riskControlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noParameters := readOptional_part [50, 49, 49, 48, 55] record.noParameters tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have targetFirmID := readOptional_part [50, 49, 48, 57, 56] record.targetFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have targetPartyID := readOptional_part [50, 49, 48, 57, 53] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have targetClientShortCode := readOptional_part [50, 49, 49, 48, 56] record.targetClientShortCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have targetLogicalAccessID := readOptional_part [50, 49, 48, 57, 57] record.targetLogicalAccessID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have eRGStatus := readOptional_part [50, 49, 49, 48, 53] record.eRGStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have oSLFlag := readOptional_part [50, 49, 49, 48, 49] record.oSLFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderSizeLimit := readOptional_part [50, 49, 49, 48, 50] record.orderSizeLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have oALFlag := readOptional_part [50, 49, 56, 48, 56] record.oALFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderAmountLimit := readOptional_part [50, 49, 56, 48, 57] record.orderAmountLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have mEPFlag := readOptional_part [50, 49, 56, 49, 49] record.mEPFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maximumLongExposure := readOptional_part [50, 49, 56, 49, 50] record.maximumLongExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have maximumShortExposure := readOptional_part [50, 49, 56, 49, 51] record.maximumShortExposure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have mEPBreachAction := readOptional_part [50, 49, 56, 49, 52] record.mEPBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have marketCondition := readOptional_part [50, 49, 56, 50, 51] record.marketCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have targetMarketPlaceID := readOptional_part [50, 49, 56, 50, 52] record.targetMarketPlaceID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have noThresholds := readOptional_part [50, 49, 56, 49, 53] record.noThresholds tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have thresholdValue := readOptional_part [50, 49, 56, 49, 55] record.thresholdValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have thresholdBreachAction := readOptional_part [50, 49, 56, 49, 54] record.thresholdBreachAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  simp only [RiskControlDetails.decode, clientMessageSendingTime, oEGINFromMember, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, requestID, ackStatus, errorCode, riskControlType, noParameters, targetFirmID, targetPartyID, targetClientShortCode, targetLogicalAccessID, securityID, securityIDSource, eMM, eRGStatus, oSLFlag, orderSizeLimit, oALFlag, orderAmountLimit, mEPFlag, maximumLongExposure, maximumShortExposure, mEPBreachAction, marketCondition, targetMarketPlaceID, noThresholds, thresholdValue, thresholdBreachAction, some_bind] <;> rfl

structure InstrumentSynchronizationList where
  resynchronizationID : Terminated 1  -- tag 20030
  noRelatedSym : Terminated 1  -- tag 146
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020

def InstrumentSynchronizationList.parts (record : InstrumentSynchronizationList) : List Part :=
  [Part.required [50, 48, 48, 51, 48] record.resynchronizationID,
   Part.required [49, 52, 54] record.noRelatedSym,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM]

def InstrumentSynchronizationList.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 51, 48]], [[49, 52, 54]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]]]

theorem InstrumentSynchronizationList.shape (record : InstrumentSynchronizationList) : record.parts.map Part.tags = InstrumentSynchronizationList.tags := rfl

def InstrumentSynchronizationList.decode (tokens : List Token) : Option InstrumentSynchronizationList := do
  let resynchronizationID ← readRequired [50, 48, 48, 51, 48] tokens
  let noRelatedSym ← readRequired [49, 52, 54] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  pure { resynchronizationID, noRelatedSym, securityID, securityIDSource, eMM }

theorem InstrumentSynchronizationList.decode_agrees (record : InstrumentSynchronizationList) (tokens : List Token)
    (agrees : ∀ tags ∈ InstrumentSynchronizationList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    InstrumentSynchronizationList.decode tokens = some record := by
  have distinct : InstrumentSynchronizationList.tags.flatten.Nodup := by decide +kernel
  have resynchronizationID := readRequired_part [50, 48, 48, 51, 48] record.resynchronizationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRelatedSym := readRequired_part [49, 52, 54] record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [InstrumentSynchronizationList.decode, resynchronizationID, noRelatedSym, securityID, securityIDSource, eMM, some_bind] <;> rfl

structure SynchronizationTime where
  resynchronizationID : Terminated 1  -- tag 20030
  lastBookInTime : Terminated 1  -- tag 20031

def SynchronizationTime.parts (record : SynchronizationTime) : List Part :=
  [Part.required [50, 48, 48, 51, 48] record.resynchronizationID,
   Part.required [50, 48, 48, 51, 49] record.lastBookInTime]

def SynchronizationTime.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]]]

theorem SynchronizationTime.shape (record : SynchronizationTime) : record.parts.map Part.tags = SynchronizationTime.tags := rfl

def SynchronizationTime.decode (tokens : List Token) : Option SynchronizationTime := do
  let resynchronizationID ← readRequired [50, 48, 48, 51, 48] tokens
  let lastBookInTime ← readRequired [50, 48, 48, 51, 49] tokens
  pure { resynchronizationID, lastBookInTime }

theorem SynchronizationTime.decode_agrees (record : SynchronizationTime) (tokens : List Token)
    (agrees : ∀ tags ∈ SynchronizationTime.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SynchronizationTime.decode tokens = some record := by
  have distinct : SynchronizationTime.tags.flatten.Nodup := by decide +kernel
  have resynchronizationID := readRequired_part [50, 48, 48, 51, 48] record.resynchronizationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastBookInTime := readRequired_part [50, 48, 48, 51, 49] record.lastBookInTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SynchronizationTime.decode, resynchronizationID, lastBookInTime, some_bind] <;> rfl

structure ClearBook where
  securityIDSource : Terminated 1  -- tag 22
  securityID : Terminated 1  -- tag 48
  eMM : Terminated 1  -- tag 20020

def ClearBook.parts (record : ClearBook) : List Part :=
  [Part.required [50, 50] record.securityIDSource,
   Part.required [52, 56] record.securityID,
   Part.required [50, 48, 48, 50, 48] record.eMM]

def ClearBook.tags : List (List (List UInt8)) :=
  [[[50, 50]], [[52, 56]], [[50, 48, 48, 50, 48]]]

theorem ClearBook.shape (record : ClearBook) : record.parts.map Part.tags = ClearBook.tags := rfl

def ClearBook.decode (tokens : List Token) : Option ClearBook := do
  let securityIDSource ← readRequired [50, 50] tokens
  let securityID ← readRequired [52, 56] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  pure { securityIDSource, securityID, eMM }

theorem ClearBook.decode_agrees (record : ClearBook) (tokens : List Token)
    (agrees : ∀ tags ∈ ClearBook.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ClearBook.decode tokens = some record := by
  have distinct : ClearBook.tags.flatten.Nodup := by decide +kernel
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ClearBook.decode, securityIDSource, securityID, eMM, some_bind] <;> rfl

structure RFQAudit where
  bookINTime : Terminated 1  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  quoteReqID : Terminated 1  -- tag 131
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Terminated 1  -- tag 20020
  noRFQCounterparts : Option (Terminated 1)  -- tag 21110
  orderOrigination : Option (Terminated 1)  -- tag 1724
  price : Option (Terminated 1)  -- tag 44
  lastQty : Option (Terminated 1)  -- tag 32
  darkExecutionInstruction : Option (Terminated 1)  -- tag 20052
  minQty : Option (Terminated 1)  -- tag 110

def RFQAudit.parts (record : RFQAudit) : List Part :=
  [Part.required [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 50, 48] record.eMM,
   Part.optional [50, 49, 49, 49, 48] record.noRFQCounterparts,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [52, 52] record.price,
   Part.optional [51, 50] record.lastQty,
   Part.optional [50, 48, 48, 53, 50] record.darkExecutionInstruction,
   Part.optional [49, 49, 48] record.minQty]

def RFQAudit.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[49, 51, 49]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[50, 49, 49, 49, 48]], [[49, 55, 50, 52]], [[52, 52]], [[51, 50]], [[50, 48, 48, 53, 50]], [[49, 49, 48]]]

theorem RFQAudit.shape (record : RFQAudit) : record.parts.map Part.tags = RFQAudit.tags := rfl

def RFQAudit.decode (tokens : List Token) : Option RFQAudit := do
  let bookINTime ← readRequired [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readRequired [50, 48, 48, 50, 48] tokens
  let noRFQCounterparts ← readOptional [50, 49, 49, 49, 48] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let price ← readOptional [52, 52] tokens
  let lastQty ← readOptional [51, 50] tokens
  let darkExecutionInstruction ← readOptional [50, 48, 48, 53, 50] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  pure { bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteReqID, securityID, securityIDSource, eMM, noRFQCounterparts, orderOrigination, price, lastQty, darkExecutionInstruction, minQty }

theorem RFQAudit.decode_agrees (record : RFQAudit) (tokens : List Token)
    (agrees : ∀ tags ∈ RFQAudit.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RFQAudit.decode tokens = some record := by
  have distinct : RFQAudit.tags.flatten.Nodup := by decide +kernel
  have bookINTime := readRequired_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have eMM := readRequired_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noRFQCounterparts := readOptional_part [50, 49, 49, 49, 48] record.noRFQCounterparts tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have darkExecutionInstruction := readOptional_part [50, 48, 48, 53, 50] record.darkExecutionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [RFQAudit.decode, bookINTime, bookOUTTime, oEGINFromME, oEGOUTToME, quoteReqID, securityID, securityIDSource, eMM, noRFQCounterparts, orderOrigination, price, lastQty, darkExecutionInstruction, minQty, some_bind] <;> rfl

structure IOINotification where
  clientMessageSendingTime : Option (Terminated 1)  -- tag 21005
  bookINTime : Option (Terminated 1)  -- tag 21002
  bookOUTTime : Option (Terminated 1)  -- tag 21003
  oEGINFromMember : Option (Terminated 1)  -- tag 5979
  oEGINFromME : Option (Terminated 1)  -- tag 7765
  oEGOUTToME : Option (Terminated 1)  -- tag 7764
  iOIID : Option (Terminated 1)  -- tag 23
  exchangeIOIID : Option (Terminated 1)  -- tag 21114
  iOIType : Terminated 1  -- tag 21113
  iOIRefID : Option (Terminated 1)  -- tag 26
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  iOIQty : Option (Terminated 1)  -- tag 27
  iOIQltyInd : Option (Terminated 1)  -- tag 25
  errorCode : Option (Terminated 1)  -- tag 9955

def IOINotification.parts (record : IOINotification) : List Part :=
  [Part.optional [50, 49, 48, 48, 53] record.clientMessageSendingTime,
   Part.optional [50, 49, 48, 48, 50] record.bookINTime,
   Part.optional [50, 49, 48, 48, 51] record.bookOUTTime,
   Part.optional [53, 57, 55, 57] record.oEGINFromMember,
   Part.optional [55, 55, 54, 53] record.oEGINFromME,
   Part.optional [55, 55, 54, 52] record.oEGOUTToME,
   Part.optional [50, 51] record.iOIID,
   Part.optional [50, 49, 49, 49, 52] record.exchangeIOIID,
   Part.required [50, 49, 49, 49, 51] record.iOIType,
   Part.optional [50, 54] record.iOIRefID,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [50, 55] record.iOIQty,
   Part.optional [50, 53] record.iOIQltyInd,
   Part.optional [57, 57, 53, 53] record.errorCode]

def IOINotification.tags : List (List (List UInt8)) :=
  [[[50, 49, 48, 48, 53]], [[50, 49, 48, 48, 50]], [[50, 49, 48, 48, 51]], [[53, 57, 55, 57]], [[55, 55, 54, 53]], [[55, 55, 54, 52]], [[50, 51]], [[50, 49, 49, 49, 52]], [[50, 49, 49, 49, 51]], [[50, 54]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[53, 52]], [[51, 56]], [[50, 55]], [[50, 53]], [[57, 57, 53, 53]]]

theorem IOINotification.shape (record : IOINotification) : record.parts.map Part.tags = IOINotification.tags := rfl

def IOINotification.decode (tokens : List Token) : Option IOINotification := do
  let clientMessageSendingTime ← readOptional [50, 49, 48, 48, 53] tokens
  let bookINTime ← readOptional [50, 49, 48, 48, 50] tokens
  let bookOUTTime ← readOptional [50, 49, 48, 48, 51] tokens
  let oEGINFromMember ← readOptional [53, 57, 55, 57] tokens
  let oEGINFromME ← readOptional [55, 55, 54, 53] tokens
  let oEGOUTToME ← readOptional [55, 55, 54, 52] tokens
  let iOIID ← readOptional [50, 51] tokens
  let exchangeIOIID ← readOptional [50, 49, 49, 49, 52] tokens
  let iOIType ← readRequired [50, 49, 49, 49, 51] tokens
  let iOIRefID ← readOptional [50, 54] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let iOIQty ← readOptional [50, 55] tokens
  let iOIQltyInd ← readOptional [50, 53] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  pure { clientMessageSendingTime, bookINTime, bookOUTTime, oEGINFromMember, oEGINFromME, oEGOUTToME, iOIID, exchangeIOIID, iOIType, iOIRefID, securityID, securityIDSource, eMM, side, orderQty, iOIQty, iOIQltyInd, errorCode }

theorem IOINotification.decode_agrees (record : IOINotification) (tokens : List Token)
    (agrees : ∀ tags ∈ IOINotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    IOINotification.decode tokens = some record := by
  have distinct : IOINotification.tags.flatten.Nodup := by decide +kernel
  have clientMessageSendingTime := readOptional_part [50, 49, 48, 48, 53] record.clientMessageSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bookINTime := readOptional_part [50, 49, 48, 48, 50] record.bookINTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have bookOUTTime := readOptional_part [50, 49, 48, 48, 51] record.bookOUTTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have oEGINFromMember := readOptional_part [53, 57, 55, 57] record.oEGINFromMember tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have oEGINFromME := readOptional_part [55, 55, 54, 53] record.oEGINFromME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have oEGOUTToME := readOptional_part [55, 55, 54, 52] record.oEGOUTToME tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have iOIID := readOptional_part [50, 51] record.iOIID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have exchangeIOIID := readOptional_part [50, 49, 49, 49, 52] record.exchangeIOIID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have iOIType := readRequired_part [50, 49, 49, 49, 51] record.iOIType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have iOIRefID := readOptional_part [50, 54] record.iOIRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have iOIQty := readOptional_part [50, 55] record.iOIQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have iOIQltyInd := readOptional_part [50, 53] record.iOIQltyInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [IOINotification.decode, clientMessageSendingTime, bookINTime, bookOUTTime, oEGINFromMember, oEGINFromME, oEGOUTToME, iOIID, exchangeIOIID, iOIType, iOIRefID, securityID, securityIDSource, eMM, side, orderQty, iOIQty, iOIQltyInd, errorCode, some_bind] <;> rfl

structure TradeCaptureReportAck where
  tradeReportID : Terminated 1  -- tag 571
  tradeID : Option (Terminated 1)  -- tag 1003
  trdRptStatus : Option (Terminated 1)  -- tag 939
  trdType : Option (Terminated 1)  -- tag 828
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  eMM : Option (Terminated 1)  -- tag 20020
  noRegulatoryTradeIDs : Option (Terminated 1)  -- tag 1907
  regulatoryTradeID : Option (Terminated 1)  -- tag 1903
  regulatoryTradeIDType : Option (Terminated 1)  -- tag 1906
  mICofSecondaryListing : Option (Terminated 1)  -- tag 21065
  preMatchingIndicator : Option (Terminated 1)  -- tag 10042
  transactTime : Option (Terminated 1)  -- tag 60
  trdRegPublicationReason : Option (Terminated 1)  -- tag 2670
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
  noNestedPartyIDs : Option (Terminated 1)  -- tag 539
  nestedPartyID : Option (Terminated 1)  -- tag 524
  nestedPartyIDSource : Option (Terminated 1)  -- tag 525
  nestedPartyRole : Option (Terminated 1)  -- tag 538
  nestedPartyRoleQualifier : Option (Terminated 1)  -- tag 2384
  orderOrigination : Option (Terminated 1)  -- tag 1724
  settlementFlag : Option (Terminated 1)  -- tag 9970
  guaranteeFlag : Option (Terminated 1)  -- tag 9971
  tradePriceCondition : Option (Terminated 1)  -- tag 1839
  vWAPBegTime : Option (Terminated 1)  -- tag 10026
  vWAPEndTime : Option (Terminated 1)  -- tag 10027
  grossTradeAmt : Option (Terminated 1)  -- tag 381
  previousDayFlag : Option (Terminated 1)  -- tag 9952
  miscFeeAmt : Option (Terminated 1)  -- tag 137
  errorCode : Option (Terminated 1)  -- tag 9955
  refMsgType : Option (Terminated 1)  -- tag 372
  centralisationDate : Option (Terminated 1)  -- tag 21068

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [57, 51, 57] record.trdRptStatus,
   Part.optional [56, 50, 56] record.trdType,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.optional [49, 57, 48, 55] record.noRegulatoryTradeIDs,
   Part.optional [49, 57, 48, 51] record.regulatoryTradeID,
   Part.optional [49, 57, 48, 54] record.regulatoryTradeIDType,
   Part.optional [50, 49, 48, 54, 53] record.mICofSecondaryListing,
   Part.optional [49, 48, 48, 52, 50] record.preMatchingIndicator,
   Part.optional [54, 48] record.transactTime,
   Part.optional [50, 54, 55, 48] record.trdRegPublicationReason,
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
   Part.optional [53, 51, 57] record.noNestedPartyIDs,
   Part.optional [53, 50, 52] record.nestedPartyID,
   Part.optional [53, 50, 53] record.nestedPartyIDSource,
   Part.optional [53, 51, 56] record.nestedPartyRole,
   Part.optional [50, 51, 56, 52] record.nestedPartyRoleQualifier,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [57, 57, 55, 48] record.settlementFlag,
   Part.optional [57, 57, 55, 49] record.guaranteeFlag,
   Part.optional [49, 56, 51, 57] record.tradePriceCondition,
   Part.optional [49, 48, 48, 50, 54] record.vWAPBegTime,
   Part.optional [49, 48, 48, 50, 55] record.vWAPEndTime,
   Part.optional [51, 56, 49] record.grossTradeAmt,
   Part.optional [57, 57, 53, 50] record.previousDayFlag,
   Part.optional [49, 51, 55] record.miscFeeAmt,
   Part.optional [57, 57, 53, 53] record.errorCode,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [50, 49, 48, 54, 56] record.centralisationDate]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[49, 48, 48, 51]], [[57, 51, 57]], [[56, 50, 56]], [[52, 56]], [[50, 50]], [[50, 48, 48, 50, 48]], [[49, 57, 48, 55]], [[49, 57, 48, 51]], [[49, 57, 48, 54]], [[50, 49, 48, 54, 53]], [[49, 48, 48, 52, 50]], [[54, 48]], [[50, 54, 55, 48]], [[53, 53, 50]], [[53, 52]], [[49]], [[54, 51, 57, 57]], [[50, 57]], [[53, 56]], [[50, 48, 49, 53, 53]], [[53, 51]], [[52, 52]], [[52, 53, 51]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[53, 51, 57]], [[53, 50, 52]], [[53, 50, 53]], [[53, 51, 56]], [[50, 51, 56, 52]], [[49, 55, 50, 52]], [[57, 57, 55, 48]], [[57, 57, 55, 49]], [[49, 56, 51, 57]], [[49, 48, 48, 50, 54]], [[49, 48, 48, 50, 55]], [[51, 56, 49]], [[57, 57, 53, 50]], [[49, 51, 55]], [[57, 57, 53, 53]], [[51, 55, 50]], [[50, 49, 48, 54, 56]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let trdRptStatus ← readOptional [57, 51, 57] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let noRegulatoryTradeIDs ← readOptional [49, 57, 48, 55] tokens
  let regulatoryTradeID ← readOptional [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readOptional [49, 57, 48, 54] tokens
  let mICofSecondaryListing ← readOptional [50, 49, 48, 54, 53] tokens
  let preMatchingIndicator ← readOptional [49, 48, 48, 52, 50] tokens
  let transactTime ← readOptional [54, 48] tokens
  let trdRegPublicationReason ← readOptional [50, 54, 55, 48] tokens
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
  let noNestedPartyIDs ← readOptional [53, 51, 57] tokens
  let nestedPartyID ← readOptional [53, 50, 52] tokens
  let nestedPartyIDSource ← readOptional [53, 50, 53] tokens
  let nestedPartyRole ← readOptional [53, 51, 56] tokens
  let nestedPartyRoleQualifier ← readOptional [50, 51, 56, 52] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let settlementFlag ← readOptional [57, 57, 55, 48] tokens
  let guaranteeFlag ← readOptional [57, 57, 55, 49] tokens
  let tradePriceCondition ← readOptional [49, 56, 51, 57] tokens
  let vWAPBegTime ← readOptional [49, 48, 48, 50, 54] tokens
  let vWAPEndTime ← readOptional [49, 48, 48, 50, 55] tokens
  let grossTradeAmt ← readOptional [51, 56, 49] tokens
  let previousDayFlag ← readOptional [57, 57, 53, 50] tokens
  let miscFeeAmt ← readOptional [49, 51, 55] tokens
  let errorCode ← readOptional [57, 57, 53, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let centralisationDate ← readOptional [50, 49, 48, 54, 56] tokens
  pure { tradeReportID, tradeID, trdRptStatus, trdType, securityID, securityIDSource, eMM, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, mICofSecondaryListing, preMatchingIndicator, transactTime, trdRegPublicationReason, noSides, side, account, accountCode, lastCapacity, text, principalCode, quantity, price, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, orderOrigination, settlementFlag, guaranteeFlag, tradePriceCondition, vWAPBegTime, vWAPEndTime, grossTradeAmt, previousDayFlag, miscFeeAmt, errorCode, refMsgType, centralisationDate }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have trdRptStatus := readOptional_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noRegulatoryTradeIDs := readOptional_part [49, 57, 48, 55] record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have regulatoryTradeID := readOptional_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have regulatoryTradeIDType := readOptional_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have mICofSecondaryListing := readOptional_part [50, 49, 48, 54, 53] record.mICofSecondaryListing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have preMatchingIndicator := readOptional_part [49, 48, 48, 52, 50] record.preMatchingIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have trdRegPublicationReason := readOptional_part [50, 54, 55, 48] record.trdRegPublicationReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noSides := readOptional_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have accountCode := readOptional_part [54, 51, 57, 57] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have principalCode := readOptional_part [50, 48, 49, 53, 53] record.principalCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have quantity := readOptional_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have partyRoleQualifi := readOptional_part [50, 51, 55, 54] record.partyRoleQualifi tokens
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
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have settlementFlag := readOptional_part [57, 57, 55, 48] record.settlementFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have guaranteeFlag := readOptional_part [57, 57, 55, 49] record.guaranteeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have tradePriceCondition := readOptional_part [49, 56, 51, 57] record.tradePriceCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have vWAPBegTime := readOptional_part [49, 48, 48, 50, 54] record.vWAPBegTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have vWAPEndTime := readOptional_part [49, 48, 48, 50, 55] record.vWAPEndTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have grossTradeAmt := readOptional_part [51, 56, 49] record.grossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have previousDayFlag := readOptional_part [57, 57, 53, 50] record.previousDayFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have miscFeeAmt := readOptional_part [49, 51, 55] record.miscFeeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have errorCode := readOptional_part [57, 57, 53, 53] record.errorCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have centralisationDate := readOptional_part [50, 49, 48, 54, 56] record.centralisationDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, tradeReportID, tradeID, trdRptStatus, trdType, securityID, securityIDSource, eMM, noRegulatoryTradeIDs, regulatoryTradeID, regulatoryTradeIDType, mICofSecondaryListing, preMatchingIndicator, transactTime, trdRegPublicationReason, noSides, side, account, accountCode, lastCapacity, text, principalCode, quantity, price, noPartyIDs, partyID, partyIDSource, partyRole, partyRoleQualifi, noNestedPartyIDs, nestedPartyID, nestedPartyIDSource, nestedPartyRole, nestedPartyRoleQualifier, orderOrigination, settlementFlag, guaranteeFlag, tradePriceCondition, vWAPBegTime, vWAPEndTime, grossTradeAmt, previousDayFlag, miscFeeAmt, errorCode, refMsgType, centralisationDate, some_bind] <;> rfl

structure FundPriceInputAck where
  clOrdID : Terminated 1  -- tag 11
  securityIDSource : Terminated 1  -- tag 22
  securityID : Terminated 1  -- tag 48
  eMM : Option (Terminated 1)  -- tag 20020
  price : Terminated 1  -- tag 44
  byPassControlFlag : Option (Terminated 1)  -- tag 10053

def FundPriceInputAck.parts (record : FundPriceInputAck) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [52, 56] record.securityID,
   Part.optional [50, 48, 48, 50, 48] record.eMM,
   Part.required [52, 52] record.price,
   Part.optional [49, 48, 48, 53, 51] record.byPassControlFlag]

def FundPriceInputAck.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[50, 50]], [[52, 56]], [[50, 48, 48, 50, 48]], [[52, 52]], [[49, 48, 48, 53, 51]]]

theorem FundPriceInputAck.shape (record : FundPriceInputAck) : record.parts.map Part.tags = FundPriceInputAck.tags := rfl

def FundPriceInputAck.decode (tokens : List Token) : Option FundPriceInputAck := do
  let clOrdID ← readRequired [49, 49] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let securityID ← readRequired [52, 56] tokens
  let eMM ← readOptional [50, 48, 48, 50, 48] tokens
  let price ← readRequired [52, 52] tokens
  let byPassControlFlag ← readOptional [49, 48, 48, 53, 51] tokens
  pure { clOrdID, securityIDSource, securityID, eMM, price, byPassControlFlag }

theorem FundPriceInputAck.decode_agrees (record : FundPriceInputAck) (tokens : List Token)
    (agrees : ∀ tags ∈ FundPriceInputAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    FundPriceInputAck.decode tokens = some record := by
  have distinct : FundPriceInputAck.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have eMM := readOptional_part [50, 48, 48, 50, 48] record.eMM tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have byPassControlFlag := readOptional_part [49, 48, 48, 53, 51] record.byPassControlFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [FundPriceInputAck.decode, clOrdID, securityIDSource, securityID, eMM, price, byPassControlFlag, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportCancelledbyReactor (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyReactor)
  | executionReportCrossOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCrossOrderAck)
  | executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay)
  | executionReportCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportCancelledbySTP (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbySTP)
  | executionReportCancelledbyCOD (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyCOD)
  | executionReportConditionalCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportConditionalCancelled)
  | executionReportCollarConfirmationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCollarConfirmationAck)
  | executionReportRefilledIcebergAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRefilledIcebergAck)
  | executionReportLPCancelRFQCancellation (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportLPCancelRFQCancellation)
  | executionReportQuoteKnockOut (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportQuoteKnockOut)
  | executionReportIcebergMinSizeTransform (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportIcebergMinSizeTransform)
  | executionReportCreatedbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCreatedbyMarketOperations)
  | executionReportRFQAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRFQAck)
  | executionReportOwnershipRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOwnershipRequestAck)
  | executionReportOrderMassStatusRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderMassStatusRequestAck)
  | executionReportCancelledFSPLimit (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledFSPLimit)
  | executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade)
  | executionReportCancelTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelTrade)
  | executionReportOrderStatus (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderStatus)
  | executionReportTriggeredbySystem (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTriggeredbySystem)
  | executionReportCancelledbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyMarketOperations)
  | massQuoteAck (header : Header) (r0 : MassQuoteAck)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | requestAckMessage (header : Header) (r0 : RequestAckMessage)
  | ownershipRequestAck (header : Header) (r0 : OwnershipRequestAck)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | askForQuote (header : Header) (r0 : AskForQuote)
  | userNotification (header : Header) (r0 : UserNotification)
  | orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport)
  | rFQNotification (header : Header) (r0 : RFQNotification)
  | rFQMatchingStatus (header : Header) (r0 : RFQMatchingStatus)
  | rFQLPMatchingStatus (header : Header) (r0 : RFQLPMatchingStatus)
  | requestForExecution (header : Header) (r0 : RequestForExecution)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | wholesaleOrderAck (header : Header) (r0 : WholesaleOrderAck)
  | eRGCommandAck (header : Header) (r0 : ERGCommandAck)
  | eRGMEPBreachAlert (header : Header) (r0 : ERGMEPBreachAlert)
  | riskControlDetails (header : Header) (r0 : RiskControlDetails)
  | instrumentSynchronizationList (header : Header) (r0 : InstrumentSynchronizationList)
  | synchronizationTime (header : Header) (r0 : SynchronizationTime)
  | clearBook (header : Header) (r0 : ClearBook)
  | rFQAudit (header : Header) (r0 : RFQAudit)
  | iOINotification (header : Header) (r0 : IOINotification)
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | fundPriceInputAck (header : Header) (r0 : FundPriceInputAck)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportCancelledbyReactor header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportCrossOrderAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportDoneForDay header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts)
  | .executionReportCancelled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportCancelledbySTP header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[97], by decide⟩] ++ r1.parts)
  | .executionReportCancelledbyCOD header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[98], by decide⟩] ++ r1.parts)
  | .executionReportConditionalCancelled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[99], by decide⟩] ++ r1.parts)
  | .executionReportCollarConfirmationAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[100], by decide⟩] ++ r1.parts)
  | .executionReportRefilledIcebergAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[101], by decide⟩] ++ r1.parts)
  | .executionReportLPCancelRFQCancellation header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[102], by decide⟩] ++ r1.parts)
  | .executionReportQuoteKnockOut header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[103], by decide⟩] ++ r1.parts)
  | .executionReportIcebergMinSizeTransform header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[104], by decide⟩] ++ r1.parts)
  | .executionReportCreatedbyMarketOperations header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[105], by decide⟩] ++ r1.parts)
  | .executionReportRFQAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[106], by decide⟩] ++ r1.parts)
  | .executionReportOwnershipRequestAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[107], by decide⟩] ++ r1.parts)
  | .executionReportOrderMassStatusRequestAck header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[109], by decide⟩] ++ r1.parts)
  | .executionReportCancelledFSPLimit header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[110], by decide⟩] ++ r1.parts)
  | .executionReportExpired header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportTrade header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts)
  | .executionReportCancelTrade header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts)
  | .executionReportOrderStatus header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts)
  | .executionReportTriggeredbySystem header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts)
  | .executionReportCancelledbyMarketOperations header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts)
  | .massQuoteAck header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .requestAckMessage header r0 => ⟨[51, 53], ⟨[85, 121], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .ownershipRequestAck header r0 => ⟨[51, 53], ⟨[85, 50, 57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .askForQuote header r0 => ⟨[51, 53], ⟨[85, 76], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userNotification header r0 => ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelReport header r0 => ⟨[51, 53], ⟨[114], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .rFQNotification header r0 => ⟨[51, 53], ⟨[85, 51, 53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .rFQMatchingStatus header r0 => ⟨[51, 53], ⟨[85, 51, 54], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .rFQLPMatchingStatus header r0 => ⟨[51, 53], ⟨[85, 51, 55], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .requestForExecution header r0 => ⟨[51, 53], ⟨[85, 77], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .wholesaleOrderAck header r0 => ⟨[51, 53], ⟨[85, 54, 53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eRGCommandAck header r0 => ⟨[51, 53], ⟨[85, 54, 57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eRGMEPBreachAlert header r0 => ⟨[51, 53], ⟨[85, 55, 54], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .riskControlDetails header r0 => ⟨[51, 53], ⟨[85, 55, 49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .instrumentSynchronizationList header r0 => ⟨[51, 53], ⟨[85, 53, 48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .synchronizationTime header r0 => ⟨[51, 53], ⟨[85, 53, 49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .clearBook header r0 => ⟨[51, 53], ⟨[85, 55, 53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .rFQAudit header r0 => ⟨[51, 53], ⟨[85, 55, 50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .iOINotification header r0 => ⟨[51, 53], ⟨[85, 55, 51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .fundPriceInputAck header r0 => ⟨[51, 53], ⟨[85, 52, 53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
          else if key.val = [49] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyReactor.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelledbyReactor.decode rest
              pure (.executionReportCancelledbyReactor header r0 r1)
            else none
          else if key.val = [50] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossOrderAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCrossOrderAck.decode rest
              pure (.executionReportCrossOrderAck header r0 r1)
            else none
          else if key.val = [51] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportDoneForDay.decode rest
              pure (.executionReportDoneForDay header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelled.decode rest
              pure (.executionReportCancelled header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportReplaced.decode rest
              pure (.executionReportReplaced header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [97] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbySTP.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelledbySTP.decode rest
              pure (.executionReportCancelledbySTP header r0 r1)
            else none
          else if key.val = [98] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyCOD.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelledbyCOD.decode rest
              pure (.executionReportCancelledbyCOD header r0 r1)
            else none
          else if key.val = [99] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportConditionalCancelled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportConditionalCancelled.decode rest
              pure (.executionReportConditionalCancelled header r0 r1)
            else none
          else if key.val = [100] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCollarConfirmationAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCollarConfirmationAck.decode rest
              pure (.executionReportCollarConfirmationAck header r0 r1)
            else none
          else if key.val = [101] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRefilledIcebergAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRefilledIcebergAck.decode rest
              pure (.executionReportRefilledIcebergAck header r0 r1)
            else none
          else if key.val = [102] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportLPCancelRFQCancellation.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportLPCancelRFQCancellation.decode rest
              pure (.executionReportLPCancelRFQCancellation header r0 r1)
            else none
          else if key.val = [103] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportQuoteKnockOut.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportQuoteKnockOut.decode rest
              pure (.executionReportQuoteKnockOut header r0 r1)
            else none
          else if key.val = [104] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportIcebergMinSizeTransform.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportIcebergMinSizeTransform.decode rest
              pure (.executionReportIcebergMinSizeTransform header r0 r1)
            else none
          else if key.val = [105] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCreatedbyMarketOperations.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCreatedbyMarketOperations.decode rest
              pure (.executionReportCreatedbyMarketOperations header r0 r1)
            else none
          else if key.val = [106] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRFQAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRFQAck.decode rest
              pure (.executionReportRFQAck header r0 r1)
            else none
          else if key.val = [107] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOwnershipRequestAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOwnershipRequestAck.decode rest
              pure (.executionReportOwnershipRequestAck header r0 r1)
            else none
          else if key.val = [109] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderMassStatusRequestAck.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOrderMassStatusRequestAck.decode rest
              pure (.executionReportOrderMassStatusRequestAck header r0 r1)
            else none
          else if key.val = [110] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledFSPLimit.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelledFSPLimit.decode rest
              pure (.executionReportCancelledFSPLimit header r0 r1)
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
          else if key.val = [70] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTrade.decode rest
              pure (.executionReportTrade header r0 r1)
            else none
          else if key.val = [72] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelTrade.decode rest
              pure (.executionReportCancelTrade header r0 r1)
            else none
          else if key.val = [73] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderStatus.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOrderStatus.decode rest
              pure (.executionReportOrderStatus header r0 r1)
            else none
          else if key.val = [76] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTriggeredbySystem.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTriggeredbySystem.decode rest
              pure (.executionReportTriggeredbySystem header r0 r1)
            else none
          else if key.val = [85] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyMarketOperations.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCancelledbyMarketOperations.decode rest
              pure (.executionReportCancelledbyMarketOperations header r0 r1)
            else none
          else none
      else if token.value.val = [98] then
        if known (Header.tags ++ MassQuoteAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuoteAck.decode rest
          pure (.massQuoteAck header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value.val = [85, 121] then
        if known (Header.tags ++ RequestAckMessage.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RequestAckMessage.decode rest
          pure (.requestAckMessage header r0)
        else none
      else if token.value.val = [85, 50, 57] then
        if known (Header.tags ++ OwnershipRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OwnershipRequestAck.decode rest
          pure (.ownershipRequestAck header r0)
        else none
      else if token.value.val = [65, 71] then
        if known (Header.tags ++ QuoteRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReject.decode rest
          pure (.quoteRequestReject header r0)
        else none
      else if token.value.val = [85, 76] then
        if known (Header.tags ++ AskForQuote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AskForQuote.decode rest
          pure (.askForQuote header r0)
        else none
      else if token.value.val = [67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
        else none
      else if token.value.val = [114] then
        if known (Header.tags ++ OrderMassCancelReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelReport.decode rest
          pure (.orderMassCancelReport header r0)
        else none
      else if token.value.val = [85, 51, 53] then
        if known (Header.tags ++ RFQNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RFQNotification.decode rest
          pure (.rFQNotification header r0)
        else none
      else if token.value.val = [85, 51, 54] then
        if known (Header.tags ++ RFQMatchingStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RFQMatchingStatus.decode rest
          pure (.rFQMatchingStatus header r0)
        else none
      else if token.value.val = [85, 51, 55] then
        if known (Header.tags ++ RFQLPMatchingStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RFQLPMatchingStatus.decode rest
          pure (.rFQLPMatchingStatus header r0)
        else none
      else if token.value.val = [85, 77] then
        if known (Header.tags ++ RequestForExecution.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RequestForExecution.decode rest
          pure (.requestForExecution header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value.val = [85, 54, 53] then
        if known (Header.tags ++ WholesaleOrderAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← WholesaleOrderAck.decode rest
          pure (.wholesaleOrderAck header r0)
        else none
      else if token.value.val = [85, 54, 57] then
        if known (Header.tags ++ ERGCommandAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ERGCommandAck.decode rest
          pure (.eRGCommandAck header r0)
        else none
      else if token.value.val = [85, 55, 54] then
        if known (Header.tags ++ ERGMEPBreachAlert.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ERGMEPBreachAlert.decode rest
          pure (.eRGMEPBreachAlert header r0)
        else none
      else if token.value.val = [85, 55, 49] then
        if known (Header.tags ++ RiskControlDetails.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RiskControlDetails.decode rest
          pure (.riskControlDetails header r0)
        else none
      else if token.value.val = [85, 53, 48] then
        if known (Header.tags ++ InstrumentSynchronizationList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← InstrumentSynchronizationList.decode rest
          pure (.instrumentSynchronizationList header r0)
        else none
      else if token.value.val = [85, 53, 49] then
        if known (Header.tags ++ SynchronizationTime.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SynchronizationTime.decode rest
          pure (.synchronizationTime header r0)
        else none
      else if token.value.val = [85, 55, 53] then
        if known (Header.tags ++ ClearBook.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ClearBook.decode rest
          pure (.clearBook header r0)
        else none
      else if token.value.val = [85, 55, 50] then
        if known (Header.tags ++ RFQAudit.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RFQAudit.decode rest
          pure (.rFQAudit header r0)
        else none
      else if token.value.val = [85, 55, 51] then
        if known (Header.tags ++ IOINotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← IOINotification.decode rest
          pure (.iOINotification header r0)
        else none
      else if token.value.val = [65, 82] then
        if known (Header.tags ++ TradeCaptureReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportAck.decode rest
          pure (.tradeCaptureReportAck header r0)
        else none
      else if token.value.val = [85, 52, 53] then
        if known (Header.tags ++ FundPriceInputAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← FundPriceInputAck.decode rest
          pure (.fundPriceInputAck header r0)
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

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelledbyReactor (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyReactor) :
    Message.decode (Message.tokens (.executionReportCancelledbyReactor header r0 r1)) = some (.executionReportCancelledbyReactor header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyReactor.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelledbyReactor.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelledbyReactor.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelledbyReactor.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelledbyReactor.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyReactor.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCrossOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCrossOrderAck) :
    Message.decode (Message.tokens (.executionReportCrossOrderAck header r0 r1)) = some (.executionReportCrossOrderAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossOrderAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCrossOrderAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCrossOrderAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCrossOrderAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCrossOrderAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossOrderAck.tags) rfl
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

theorem Message.decode_executionReportCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelled) :
    Message.decode (Message.tokens (.executionReportCancelled header r0 r1)) = some (.executionReportCancelled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelled.tags) rfl
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

theorem Message.decode_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decode (Message.tokens (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelledbySTP (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbySTP) :
    Message.decode (Message.tokens (.executionReportCancelledbySTP header r0 r1)) = some (.executionReportCancelledbySTP header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[97], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbySTP.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[97], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelledbySTP.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[97], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[97], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelledbySTP.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelledbySTP.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[97], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelledbySTP.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[97], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbySTP.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelledbyCOD (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyCOD) :
    Message.decode (Message.tokens (.executionReportCancelledbyCOD header r0 r1)) = some (.executionReportCancelledbyCOD header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[98], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyCOD.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[98], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelledbyCOD.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[98], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[98], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelledbyCOD.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelledbyCOD.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[98], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelledbyCOD.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[98], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyCOD.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportConditionalCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportConditionalCancelled) :
    Message.decode (Message.tokens (.executionReportConditionalCancelled header r0 r1)) = some (.executionReportConditionalCancelled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[99], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportConditionalCancelled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[99], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportConditionalCancelled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[99], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[99], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportConditionalCancelled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportConditionalCancelled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[99], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportConditionalCancelled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[99], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportConditionalCancelled.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCollarConfirmationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCollarConfirmationAck) :
    Message.decode (Message.tokens (.executionReportCollarConfirmationAck header r0 r1)) = some (.executionReportCollarConfirmationAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[100], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCollarConfirmationAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[100], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCollarConfirmationAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[100], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[100], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCollarConfirmationAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCollarConfirmationAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[100], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCollarConfirmationAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[100], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCollarConfirmationAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRefilledIcebergAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRefilledIcebergAck) :
    Message.decode (Message.tokens (.executionReportRefilledIcebergAck header r0 r1)) = some (.executionReportRefilledIcebergAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[101], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRefilledIcebergAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[101], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRefilledIcebergAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[101], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[101], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRefilledIcebergAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRefilledIcebergAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[101], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRefilledIcebergAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[101], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRefilledIcebergAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportLPCancelRFQCancellation (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportLPCancelRFQCancellation) :
    Message.decode (Message.tokens (.executionReportLPCancelRFQCancellation header r0 r1)) = some (.executionReportLPCancelRFQCancellation header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[102], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportLPCancelRFQCancellation.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[102], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportLPCancelRFQCancellation.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[102], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[102], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportLPCancelRFQCancellation.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportLPCancelRFQCancellation.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[102], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportLPCancelRFQCancellation.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[102], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportLPCancelRFQCancellation.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportQuoteKnockOut (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportQuoteKnockOut) :
    Message.decode (Message.tokens (.executionReportQuoteKnockOut header r0 r1)) = some (.executionReportQuoteKnockOut header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[103], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportQuoteKnockOut.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[103], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportQuoteKnockOut.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[103], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[103], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportQuoteKnockOut.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportQuoteKnockOut.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[103], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportQuoteKnockOut.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[103], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportQuoteKnockOut.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportIcebergMinSizeTransform (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportIcebergMinSizeTransform) :
    Message.decode (Message.tokens (.executionReportIcebergMinSizeTransform header r0 r1)) = some (.executionReportIcebergMinSizeTransform header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[104], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportIcebergMinSizeTransform.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[104], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportIcebergMinSizeTransform.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[104], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[104], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportIcebergMinSizeTransform.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportIcebergMinSizeTransform.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[104], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportIcebergMinSizeTransform.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[104], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportIcebergMinSizeTransform.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCreatedbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCreatedbyMarketOperations) :
    Message.decode (Message.tokens (.executionReportCreatedbyMarketOperations header r0 r1)) = some (.executionReportCreatedbyMarketOperations header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[105], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCreatedbyMarketOperations.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[105], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCreatedbyMarketOperations.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[105], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[105], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCreatedbyMarketOperations.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCreatedbyMarketOperations.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[105], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCreatedbyMarketOperations.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[105], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCreatedbyMarketOperations.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRFQAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRFQAck) :
    Message.decode (Message.tokens (.executionReportRFQAck header r0 r1)) = some (.executionReportRFQAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[106], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRFQAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[106], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRFQAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[106], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[106], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRFQAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRFQAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[106], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRFQAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[106], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRFQAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportOwnershipRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOwnershipRequestAck) :
    Message.decode (Message.tokens (.executionReportOwnershipRequestAck header r0 r1)) = some (.executionReportOwnershipRequestAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[107], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOwnershipRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[107], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOwnershipRequestAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[107], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[107], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOwnershipRequestAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOwnershipRequestAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[107], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOwnershipRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[107], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOwnershipRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportOrderMassStatusRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderMassStatusRequestAck) :
    Message.decode (Message.tokens (.executionReportOrderMassStatusRequestAck header r0 r1)) = some (.executionReportOrderMassStatusRequestAck header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[109], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderMassStatusRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[109], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOrderMassStatusRequestAck.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[109], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[109], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOrderMassStatusRequestAck.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOrderMassStatusRequestAck.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[109], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOrderMassStatusRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[109], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderMassStatusRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelledFSPLimit (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledFSPLimit) :
    Message.decode (Message.tokens (.executionReportCancelledFSPLimit header r0 r1)) = some (.executionReportCancelledFSPLimit header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[110], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledFSPLimit.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[110], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelledFSPLimit.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[110], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[110], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelledFSPLimit.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelledFSPLimit.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[110], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelledFSPLimit.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[110], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledFSPLimit.tags) rfl
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

theorem Message.decode_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decode (Message.tokens (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[70], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelTrade) :
    Message.decode (Message.tokens (.executionReportCancelTrade header r0 r1)) = some (.executionReportCancelTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[72], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[72], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelTrade.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportOrderStatus (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderStatus) :
    Message.decode (Message.tokens (.executionReportOrderStatus header r0 r1)) = some (.executionReportOrderStatus header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderStatus.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOrderStatus.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[73], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[73], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOrderStatus.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOrderStatus.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOrderStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderStatus.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTriggeredbySystem (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTriggeredbySystem) :
    Message.decode (Message.tokens (.executionReportTriggeredbySystem header r0 r1)) = some (.executionReportTriggeredbySystem header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTriggeredbySystem.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTriggeredbySystem.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[76], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[76], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTriggeredbySystem.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTriggeredbySystem.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTriggeredbySystem.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTriggeredbySystem.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCancelledbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyMarketOperations) :
    Message.decode (Message.tokens (.executionReportCancelledbyMarketOperations header r0 r1)) = some (.executionReportCancelledbyMarketOperations header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyMarketOperations.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCancelledbyMarketOperations.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[85], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCancelledbyMarketOperations.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCancelledbyMarketOperations.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCancelledbyMarketOperations.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyMarketOperations.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuoteAck (header : Header) (r0 : MassQuoteAck) :
    Message.decode (Message.tokens (.massQuoteAck header r0)) = some (.massQuoteAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAck.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuoteAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_requestAckMessage (header : Header) (r0 : RequestAckMessage) :
    Message.decode (Message.tokens (.requestAckMessage header r0)) = some (.requestAckMessage header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RequestAckMessage.tags) rfl rfl (by decide +kernel))
  have c1 := RequestAckMessage.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RequestAckMessage.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RequestAckMessage.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_ownershipRequestAck (header : Header) (r0 : OwnershipRequestAck) :
    Message.decode (Message.tokens (.ownershipRequestAck header r0)) = some (.ownershipRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OwnershipRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := OwnershipRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OwnershipRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OwnershipRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decode (Message.tokens (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_askForQuote (header : Header) (r0 : AskForQuote) :
    Message.decode (Message.tokens (.askForQuote header r0)) = some (.askForQuote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AskForQuote.tags) rfl rfl (by decide +kernel))
  have c1 := AskForQuote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AskForQuote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AskForQuote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decode (Message.tokens (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_rFQNotification (header : Header) (r0 : RFQNotification) :
    Message.decode (Message.tokens (.rFQNotification header r0)) = some (.rFQNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RFQNotification.tags) rfl rfl (by decide +kernel))
  have c1 := RFQNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RFQNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RFQNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_rFQMatchingStatus (header : Header) (r0 : RFQMatchingStatus) :
    Message.decode (Message.tokens (.rFQMatchingStatus header r0)) = some (.rFQMatchingStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RFQMatchingStatus.tags) rfl rfl (by decide +kernel))
  have c1 := RFQMatchingStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RFQMatchingStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RFQMatchingStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_rFQLPMatchingStatus (header : Header) (r0 : RFQLPMatchingStatus) :
    Message.decode (Message.tokens (.rFQLPMatchingStatus header r0)) = some (.rFQLPMatchingStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RFQLPMatchingStatus.tags) rfl rfl (by decide +kernel))
  have c1 := RFQLPMatchingStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RFQLPMatchingStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RFQLPMatchingStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_requestForExecution (header : Header) (r0 : RequestForExecution) :
    Message.decode (Message.tokens (.requestForExecution header r0)) = some (.requestForExecution header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RequestForExecution.tags) rfl rfl (by decide +kernel))
  have c1 := RequestForExecution.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RequestForExecution.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RequestForExecution.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_wholesaleOrderAck (header : Header) (r0 : WholesaleOrderAck) :
    Message.decode (Message.tokens (.wholesaleOrderAck header r0)) = some (.wholesaleOrderAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (WholesaleOrderAck.tags) rfl rfl (by decide +kernel))
  have c1 := WholesaleOrderAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (WholesaleOrderAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ WholesaleOrderAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_eRGCommandAck (header : Header) (r0 : ERGCommandAck) :
    Message.decode (Message.tokens (.eRGCommandAck header r0)) = some (.eRGCommandAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ERGCommandAck.tags) rfl rfl (by decide +kernel))
  have c1 := ERGCommandAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ERGCommandAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ERGCommandAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_eRGMEPBreachAlert (header : Header) (r0 : ERGMEPBreachAlert) :
    Message.decode (Message.tokens (.eRGMEPBreachAlert header r0)) = some (.eRGMEPBreachAlert header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ERGMEPBreachAlert.tags) rfl rfl (by decide +kernel))
  have c1 := ERGMEPBreachAlert.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ERGMEPBreachAlert.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ERGMEPBreachAlert.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_riskControlDetails (header : Header) (r0 : RiskControlDetails) :
    Message.decode (Message.tokens (.riskControlDetails header r0)) = some (.riskControlDetails header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RiskControlDetails.tags) rfl rfl (by decide +kernel))
  have c1 := RiskControlDetails.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RiskControlDetails.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RiskControlDetails.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_instrumentSynchronizationList (header : Header) (r0 : InstrumentSynchronizationList) :
    Message.decode (Message.tokens (.instrumentSynchronizationList header r0)) = some (.instrumentSynchronizationList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (InstrumentSynchronizationList.tags) rfl rfl (by decide +kernel))
  have c1 := InstrumentSynchronizationList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (InstrumentSynchronizationList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ InstrumentSynchronizationList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_synchronizationTime (header : Header) (r0 : SynchronizationTime) :
    Message.decode (Message.tokens (.synchronizationTime header r0)) = some (.synchronizationTime header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SynchronizationTime.tags) rfl rfl (by decide +kernel))
  have c1 := SynchronizationTime.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SynchronizationTime.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SynchronizationTime.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_clearBook (header : Header) (r0 : ClearBook) :
    Message.decode (Message.tokens (.clearBook header r0)) = some (.clearBook header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ClearBook.tags) rfl rfl (by decide +kernel))
  have c1 := ClearBook.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ClearBook.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ClearBook.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_rFQAudit (header : Header) (r0 : RFQAudit) :
    Message.decode (Message.tokens (.rFQAudit header r0)) = some (.rFQAudit header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RFQAudit.tags) rfl rfl (by decide +kernel))
  have c1 := RFQAudit.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RFQAudit.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RFQAudit.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_iOINotification (header : Header) (r0 : IOINotification) :
    Message.decode (Message.tokens (.iOINotification header r0)) = some (.iOINotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (IOINotification.tags) rfl rfl (by decide +kernel))
  have c1 := IOINotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (IOINotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ IOINotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decode (Message.tokens (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_fundPriceInputAck (header : Header) (r0 : FundPriceInputAck) :
    Message.decode (Message.tokens (.fundPriceInputAck header r0)) = some (.fundPriceInputAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (FundPriceInputAck.tags) rfl rfl (by decide +kernel))
  have c1 := FundPriceInputAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (FundPriceInputAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ FundPriceInputAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportCancelledbyReactor header r0 r1 => exact Message.decode_executionReportCancelledbyReactor header r0 r1
  | executionReportCrossOrderAck header r0 r1 => exact Message.decode_executionReportCrossOrderAck header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decode_executionReportDoneForDay header r0 r1
  | executionReportCancelled header r0 r1 => exact Message.decode_executionReportCancelled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportCancelledbySTP header r0 r1 => exact Message.decode_executionReportCancelledbySTP header r0 r1
  | executionReportCancelledbyCOD header r0 r1 => exact Message.decode_executionReportCancelledbyCOD header r0 r1
  | executionReportConditionalCancelled header r0 r1 => exact Message.decode_executionReportConditionalCancelled header r0 r1
  | executionReportCollarConfirmationAck header r0 r1 => exact Message.decode_executionReportCollarConfirmationAck header r0 r1
  | executionReportRefilledIcebergAck header r0 r1 => exact Message.decode_executionReportRefilledIcebergAck header r0 r1
  | executionReportLPCancelRFQCancellation header r0 r1 => exact Message.decode_executionReportLPCancelRFQCancellation header r0 r1
  | executionReportQuoteKnockOut header r0 r1 => exact Message.decode_executionReportQuoteKnockOut header r0 r1
  | executionReportIcebergMinSizeTransform header r0 r1 => exact Message.decode_executionReportIcebergMinSizeTransform header r0 r1
  | executionReportCreatedbyMarketOperations header r0 r1 => exact Message.decode_executionReportCreatedbyMarketOperations header r0 r1
  | executionReportRFQAck header r0 r1 => exact Message.decode_executionReportRFQAck header r0 r1
  | executionReportOwnershipRequestAck header r0 r1 => exact Message.decode_executionReportOwnershipRequestAck header r0 r1
  | executionReportOrderMassStatusRequestAck header r0 r1 => exact Message.decode_executionReportOrderMassStatusRequestAck header r0 r1
  | executionReportCancelledFSPLimit header r0 r1 => exact Message.decode_executionReportCancelledFSPLimit header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decode_executionReportExpired header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decode_executionReportTrade header r0 r1
  | executionReportCancelTrade header r0 r1 => exact Message.decode_executionReportCancelTrade header r0 r1
  | executionReportOrderStatus header r0 r1 => exact Message.decode_executionReportOrderStatus header r0 r1
  | executionReportTriggeredbySystem header r0 r1 => exact Message.decode_executionReportTriggeredbySystem header r0 r1
  | executionReportCancelledbyMarketOperations header r0 r1 => exact Message.decode_executionReportCancelledbyMarketOperations header r0 r1
  | massQuoteAck header r0 => exact Message.decode_massQuoteAck header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | requestAckMessage header r0 => exact Message.decode_requestAckMessage header r0
  | ownershipRequestAck header r0 => exact Message.decode_ownershipRequestAck header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | askForQuote header r0 => exact Message.decode_askForQuote header r0
  | userNotification header r0 => exact Message.decode_userNotification header r0
  | orderMassCancelReport header r0 => exact Message.decode_orderMassCancelReport header r0
  | rFQNotification header r0 => exact Message.decode_rFQNotification header r0
  | rFQMatchingStatus header r0 => exact Message.decode_rFQMatchingStatus header r0
  | rFQLPMatchingStatus header r0 => exact Message.decode_rFQLPMatchingStatus header r0
  | requestForExecution header r0 => exact Message.decode_requestForExecution header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | wholesaleOrderAck header r0 => exact Message.decode_wholesaleOrderAck header r0
  | eRGCommandAck header r0 => exact Message.decode_eRGCommandAck header r0
  | eRGMEPBreachAlert header r0 => exact Message.decode_eRGMEPBreachAlert header r0
  | riskControlDetails header r0 => exact Message.decode_riskControlDetails header r0
  | instrumentSynchronizationList header r0 => exact Message.decode_instrumentSynchronizationList header r0
  | synchronizationTime header r0 => exact Message.decode_synchronizationTime header r0
  | clearBook header r0 => exact Message.decode_clearBook header r0
  | rFQAudit header r0 => exact Message.decode_rFQAudit header r0
  | iOINotification header r0 => exact Message.decode_iOINotification header r0
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | fundPriceInputAck header r0 => exact Message.decode_fundPriceInputAck header r0

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

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportCancelledbyReactor (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyReactor) :
    Message.decodeBytes (Message.encode (.executionReportCancelledbyReactor header r0 r1)) = some (.executionReportCancelledbyReactor header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyReactor.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelledbyReactor header r0 r1

theorem Message.decodeBytes_executionReportCrossOrderAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCrossOrderAck) :
    Message.decodeBytes (Message.encode (.executionReportCrossOrderAck header r0 r1)) = some (.executionReportCrossOrderAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossOrderAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCrossOrderAck header r0 r1

theorem Message.decodeBytes_executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay) :
    Message.decodeBytes (Message.encode (.executionReportDoneForDay header r0 r1)) = some (.executionReportDoneForDay header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportDoneForDay header r0 r1

theorem Message.decodeBytes_executionReportCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelled) :
    Message.decodeBytes (Message.encode (.executionReportCancelled header r0 r1)) = some (.executionReportCancelled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelled header r0 r1

theorem Message.decodeBytes_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decodeBytes (Message.encode (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplaced header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportCancelledbySTP (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbySTP) :
    Message.decodeBytes (Message.encode (.executionReportCancelledbySTP header r0 r1)) = some (.executionReportCancelledbySTP header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[97], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbySTP.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelledbySTP header r0 r1

theorem Message.decodeBytes_executionReportCancelledbyCOD (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyCOD) :
    Message.decodeBytes (Message.encode (.executionReportCancelledbyCOD header r0 r1)) = some (.executionReportCancelledbyCOD header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[98], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyCOD.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelledbyCOD header r0 r1

theorem Message.decodeBytes_executionReportConditionalCancelled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportConditionalCancelled) :
    Message.decodeBytes (Message.encode (.executionReportConditionalCancelled header r0 r1)) = some (.executionReportConditionalCancelled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[99], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportConditionalCancelled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportConditionalCancelled header r0 r1

theorem Message.decodeBytes_executionReportCollarConfirmationAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCollarConfirmationAck) :
    Message.decodeBytes (Message.encode (.executionReportCollarConfirmationAck header r0 r1)) = some (.executionReportCollarConfirmationAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[100], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCollarConfirmationAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCollarConfirmationAck header r0 r1

theorem Message.decodeBytes_executionReportRefilledIcebergAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRefilledIcebergAck) :
    Message.decodeBytes (Message.encode (.executionReportRefilledIcebergAck header r0 r1)) = some (.executionReportRefilledIcebergAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[101], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRefilledIcebergAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRefilledIcebergAck header r0 r1

theorem Message.decodeBytes_executionReportLPCancelRFQCancellation (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportLPCancelRFQCancellation) :
    Message.decodeBytes (Message.encode (.executionReportLPCancelRFQCancellation header r0 r1)) = some (.executionReportLPCancelRFQCancellation header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[102], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportLPCancelRFQCancellation.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportLPCancelRFQCancellation header r0 r1

theorem Message.decodeBytes_executionReportQuoteKnockOut (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportQuoteKnockOut) :
    Message.decodeBytes (Message.encode (.executionReportQuoteKnockOut header r0 r1)) = some (.executionReportQuoteKnockOut header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[103], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportQuoteKnockOut.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportQuoteKnockOut header r0 r1

theorem Message.decodeBytes_executionReportIcebergMinSizeTransform (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportIcebergMinSizeTransform) :
    Message.decodeBytes (Message.encode (.executionReportIcebergMinSizeTransform header r0 r1)) = some (.executionReportIcebergMinSizeTransform header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[104], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportIcebergMinSizeTransform.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportIcebergMinSizeTransform header r0 r1

theorem Message.decodeBytes_executionReportCreatedbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCreatedbyMarketOperations) :
    Message.decodeBytes (Message.encode (.executionReportCreatedbyMarketOperations header r0 r1)) = some (.executionReportCreatedbyMarketOperations header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[105], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCreatedbyMarketOperations.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCreatedbyMarketOperations header r0 r1

theorem Message.decodeBytes_executionReportRFQAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRFQAck) :
    Message.decodeBytes (Message.encode (.executionReportRFQAck header r0 r1)) = some (.executionReportRFQAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[106], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRFQAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRFQAck header r0 r1

theorem Message.decodeBytes_executionReportOwnershipRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOwnershipRequestAck) :
    Message.decodeBytes (Message.encode (.executionReportOwnershipRequestAck header r0 r1)) = some (.executionReportOwnershipRequestAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[107], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOwnershipRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOwnershipRequestAck header r0 r1

theorem Message.decodeBytes_executionReportOrderMassStatusRequestAck (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderMassStatusRequestAck) :
    Message.decodeBytes (Message.encode (.executionReportOrderMassStatusRequestAck header r0 r1)) = some (.executionReportOrderMassStatusRequestAck header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[109], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderMassStatusRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOrderMassStatusRequestAck header r0 r1

theorem Message.decodeBytes_executionReportCancelledFSPLimit (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledFSPLimit) :
    Message.decodeBytes (Message.encode (.executionReportCancelledFSPLimit header r0 r1)) = some (.executionReportCancelledFSPLimit header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[110], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledFSPLimit.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelledFSPLimit header r0 r1

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

theorem Message.decodeBytes_executionReportTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTrade) :
    Message.decodeBytes (Message.encode (.executionReportTrade header r0 r1)) = some (.executionReportTrade header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[70], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTrade header r0 r1

theorem Message.decodeBytes_executionReportCancelTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelTrade) :
    Message.decodeBytes (Message.encode (.executionReportCancelTrade header r0 r1)) = some (.executionReportCancelTrade header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[72], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelTrade header r0 r1

theorem Message.decodeBytes_executionReportOrderStatus (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderStatus) :
    Message.decodeBytes (Message.encode (.executionReportOrderStatus header r0 r1)) = some (.executionReportOrderStatus header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[73], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderStatus.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOrderStatus header r0 r1

theorem Message.decodeBytes_executionReportTriggeredbySystem (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTriggeredbySystem) :
    Message.decodeBytes (Message.encode (.executionReportTriggeredbySystem header r0 r1)) = some (.executionReportTriggeredbySystem header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[76], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTriggeredbySystem.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTriggeredbySystem header r0 r1

theorem Message.decodeBytes_executionReportCancelledbyMarketOperations (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCancelledbyMarketOperations) :
    Message.decodeBytes (Message.encode (.executionReportCancelledbyMarketOperations header r0 r1)) = some (.executionReportCancelledbyMarketOperations header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCancelledbyMarketOperations.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCancelledbyMarketOperations header r0 r1

theorem Message.decodeBytes_massQuoteAck (header : Header) (r0 : MassQuoteAck) :
    Message.decodeBytes (Message.encode (.massQuoteAck header r0)) = some (.massQuoteAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[98], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuoteAck header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_requestAckMessage (header : Header) (r0 : RequestAckMessage) :
    Message.decodeBytes (Message.encode (.requestAckMessage header r0)) = some (.requestAckMessage header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 121], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RequestAckMessage.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_requestAckMessage header r0

theorem Message.decodeBytes_ownershipRequestAck (header : Header) (r0 : OwnershipRequestAck) :
    Message.decodeBytes (Message.encode (.ownershipRequestAck header r0)) = some (.ownershipRequestAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 50, 57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OwnershipRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_ownershipRequestAck header r0

theorem Message.decodeBytes_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decodeBytes (Message.encode (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReject header r0

theorem Message.decodeBytes_askForQuote (header : Header) (r0 : AskForQuote) :
    Message.decodeBytes (Message.encode (.askForQuote header r0)) = some (.askForQuote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 76], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AskForQuote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_askForQuote header r0

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decodeBytes (Message.encode (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[114], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReport header r0

theorem Message.decodeBytes_rFQNotification (header : Header) (r0 : RFQNotification) :
    Message.decodeBytes (Message.encode (.rFQNotification header r0)) = some (.rFQNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 51, 53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RFQNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_rFQNotification header r0

theorem Message.decodeBytes_rFQMatchingStatus (header : Header) (r0 : RFQMatchingStatus) :
    Message.decodeBytes (Message.encode (.rFQMatchingStatus header r0)) = some (.rFQMatchingStatus header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 51, 54], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RFQMatchingStatus.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_rFQMatchingStatus header r0

theorem Message.decodeBytes_rFQLPMatchingStatus (header : Header) (r0 : RFQLPMatchingStatus) :
    Message.decodeBytes (Message.encode (.rFQLPMatchingStatus header r0)) = some (.rFQLPMatchingStatus header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 51, 55], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RFQLPMatchingStatus.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_rFQLPMatchingStatus header r0

theorem Message.decodeBytes_requestForExecution (header : Header) (r0 : RequestForExecution) :
    Message.decodeBytes (Message.encode (.requestForExecution header r0)) = some (.requestForExecution header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 77], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RequestForExecution.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_requestForExecution header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_wholesaleOrderAck (header : Header) (r0 : WholesaleOrderAck) :
    Message.decodeBytes (Message.encode (.wholesaleOrderAck header r0)) = some (.wholesaleOrderAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ WholesaleOrderAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_wholesaleOrderAck header r0

theorem Message.decodeBytes_eRGCommandAck (header : Header) (r0 : ERGCommandAck) :
    Message.decodeBytes (Message.encode (.eRGCommandAck header r0)) = some (.eRGCommandAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 54, 57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ERGCommandAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eRGCommandAck header r0

theorem Message.decodeBytes_eRGMEPBreachAlert (header : Header) (r0 : ERGMEPBreachAlert) :
    Message.decodeBytes (Message.encode (.eRGMEPBreachAlert header r0)) = some (.eRGMEPBreachAlert header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 54], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ERGMEPBreachAlert.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eRGMEPBreachAlert header r0

theorem Message.decodeBytes_riskControlDetails (header : Header) (r0 : RiskControlDetails) :
    Message.decodeBytes (Message.encode (.riskControlDetails header r0)) = some (.riskControlDetails header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RiskControlDetails.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_riskControlDetails header r0

theorem Message.decodeBytes_instrumentSynchronizationList (header : Header) (r0 : InstrumentSynchronizationList) :
    Message.decodeBytes (Message.encode (.instrumentSynchronizationList header r0)) = some (.instrumentSynchronizationList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 53, 48], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ InstrumentSynchronizationList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_instrumentSynchronizationList header r0

theorem Message.decodeBytes_synchronizationTime (header : Header) (r0 : SynchronizationTime) :
    Message.decodeBytes (Message.encode (.synchronizationTime header r0)) = some (.synchronizationTime header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 53, 49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SynchronizationTime.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_synchronizationTime header r0

theorem Message.decodeBytes_clearBook (header : Header) (r0 : ClearBook) :
    Message.decodeBytes (Message.encode (.clearBook header r0)) = some (.clearBook header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ClearBook.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_clearBook header r0

theorem Message.decodeBytes_rFQAudit (header : Header) (r0 : RFQAudit) :
    Message.decodeBytes (Message.encode (.rFQAudit header r0)) = some (.rFQAudit header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 50], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RFQAudit.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_rFQAudit header r0

theorem Message.decodeBytes_iOINotification (header : Header) (r0 : IOINotification) :
    Message.decodeBytes (Message.encode (.iOINotification header r0)) = some (.iOINotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 55, 51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ IOINotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_iOINotification header r0

theorem Message.decodeBytes_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAck header r0

theorem Message.decodeBytes_fundPriceInputAck (header : Header) (r0 : FundPriceInputAck) :
    Message.decodeBytes (Message.encode (.fundPriceInputAck header r0)) = some (.fundPriceInputAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 52, 53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ FundPriceInputAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_fundPriceInputAck header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportCancelledbyReactor header r0 r1 => exact Message.decodeBytes_executionReportCancelledbyReactor header r0 r1
  | executionReportCrossOrderAck header r0 r1 => exact Message.decodeBytes_executionReportCrossOrderAck header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decodeBytes_executionReportDoneForDay header r0 r1
  | executionReportCancelled header r0 r1 => exact Message.decodeBytes_executionReportCancelled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportCancelledbySTP header r0 r1 => exact Message.decodeBytes_executionReportCancelledbySTP header r0 r1
  | executionReportCancelledbyCOD header r0 r1 => exact Message.decodeBytes_executionReportCancelledbyCOD header r0 r1
  | executionReportConditionalCancelled header r0 r1 => exact Message.decodeBytes_executionReportConditionalCancelled header r0 r1
  | executionReportCollarConfirmationAck header r0 r1 => exact Message.decodeBytes_executionReportCollarConfirmationAck header r0 r1
  | executionReportRefilledIcebergAck header r0 r1 => exact Message.decodeBytes_executionReportRefilledIcebergAck header r0 r1
  | executionReportLPCancelRFQCancellation header r0 r1 => exact Message.decodeBytes_executionReportLPCancelRFQCancellation header r0 r1
  | executionReportQuoteKnockOut header r0 r1 => exact Message.decodeBytes_executionReportQuoteKnockOut header r0 r1
  | executionReportIcebergMinSizeTransform header r0 r1 => exact Message.decodeBytes_executionReportIcebergMinSizeTransform header r0 r1
  | executionReportCreatedbyMarketOperations header r0 r1 => exact Message.decodeBytes_executionReportCreatedbyMarketOperations header r0 r1
  | executionReportRFQAck header r0 r1 => exact Message.decodeBytes_executionReportRFQAck header r0 r1
  | executionReportOwnershipRequestAck header r0 r1 => exact Message.decodeBytes_executionReportOwnershipRequestAck header r0 r1
  | executionReportOrderMassStatusRequestAck header r0 r1 => exact Message.decodeBytes_executionReportOrderMassStatusRequestAck header r0 r1
  | executionReportCancelledFSPLimit header r0 r1 => exact Message.decodeBytes_executionReportCancelledFSPLimit header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decodeBytes_executionReportExpired header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportTrade header r0 r1 => exact Message.decodeBytes_executionReportTrade header r0 r1
  | executionReportCancelTrade header r0 r1 => exact Message.decodeBytes_executionReportCancelTrade header r0 r1
  | executionReportOrderStatus header r0 r1 => exact Message.decodeBytes_executionReportOrderStatus header r0 r1
  | executionReportTriggeredbySystem header r0 r1 => exact Message.decodeBytes_executionReportTriggeredbySystem header r0 r1
  | executionReportCancelledbyMarketOperations header r0 r1 => exact Message.decodeBytes_executionReportCancelledbyMarketOperations header r0 r1
  | massQuoteAck header r0 => exact Message.decodeBytes_massQuoteAck header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | requestAckMessage header r0 => exact Message.decodeBytes_requestAckMessage header r0
  | ownershipRequestAck header r0 => exact Message.decodeBytes_ownershipRequestAck header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | askForQuote header r0 => exact Message.decodeBytes_askForQuote header r0
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0
  | orderMassCancelReport header r0 => exact Message.decodeBytes_orderMassCancelReport header r0
  | rFQNotification header r0 => exact Message.decodeBytes_rFQNotification header r0
  | rFQMatchingStatus header r0 => exact Message.decodeBytes_rFQMatchingStatus header r0
  | rFQLPMatchingStatus header r0 => exact Message.decodeBytes_rFQLPMatchingStatus header r0
  | requestForExecution header r0 => exact Message.decodeBytes_requestForExecution header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | wholesaleOrderAck header r0 => exact Message.decodeBytes_wholesaleOrderAck header r0
  | eRGCommandAck header r0 => exact Message.decodeBytes_eRGCommandAck header r0
  | eRGMEPBreachAlert header r0 => exact Message.decodeBytes_eRGMEPBreachAlert header r0
  | riskControlDetails header r0 => exact Message.decodeBytes_riskControlDetails header r0
  | instrumentSynchronizationList header r0 => exact Message.decodeBytes_instrumentSynchronizationList header r0
  | synchronizationTime header r0 => exact Message.decodeBytes_synchronizationTime header r0
  | clearBook header r0 => exact Message.decodeBytes_clearBook header r0
  | rFQAudit header r0 => exact Message.decodeBytes_rFQAudit header r0
  | iOINotification header r0 => exact Message.decodeBytes_iOINotification header r0
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | fundPriceInputAck header r0 => exact Message.decodeBytes_fundPriceInputAck header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.EuronextOptiqOrderentryFixV665Exchange
