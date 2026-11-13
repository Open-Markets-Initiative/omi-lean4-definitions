import Wire

/-!
# The Members Exchange Order Entry v1.10.a, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.MemxMemxoptionsOrderentryFixV110AClient

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

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  businessRejectReason : Terminated 1  -- tag 380
  refMsgType : Option (Terminated 1)  -- tag 372
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 56, 48]], [[51, 55, 50]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, businessRejectReason, refMsgType, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, businessRejectReason, refMsgType, text, some_bind] <;> rfl

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

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  symbol : Option (Terminated 1)  -- tag 55
  maturityDate : Option (Terminated 1)  -- tag 541
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  positionEffect : Option (Terminated 1)  -- tag 77
  tradingCapacity : Terminated 1  -- tag 1815
  execInst : Option (Terminated 1)  -- tag 18
  transactTime : Terminated 1  -- tag 60
  repriceFrequency : Option (Terminated 1)  -- tag 21020
  repriceBehaviorType : Option (Terminated 1)  -- tag 21021
  mtpGroupID : Option (Terminated 1)  -- tag 2362
  matchTradePrevention : Option (Terminated 1)  -- tag 21001
  riskGroupID : Option (Terminated 1)  -- tag 21005
  cancelGroupID : Option (Terminated 1)  -- tag 21000
  noPartyIDs : List NoPartyIDs  -- tag 453

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.optional [55, 55] record.positionEffect,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [49, 56] record.execInst,
   Part.required [54, 48] record.transactTime,
   Part.optional [50, 49, 48, 50, 48] record.repriceFrequency,
   Part.optional [50, 49, 48, 50, 49] record.repriceBehaviorType,
   Part.optional [50, 51, 54, 50] record.mtpGroupID,
   Part.optional [50, 49, 48, 48, 49] record.matchTradePrevention,
   Part.optional [50, 49, 48, 48, 53] record.riskGroupID,
   Part.optional [50, 49, 48, 48, 48] record.cancelGroupID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[55, 55]], [[49, 56, 49, 53]], [[49, 56]], [[54, 48]], [[50, 49, 48, 50, 48]], [[50, 49, 48, 50, 49]], [[50, 51, 54, 50]], [[50, 49, 48, 48, 49]], [[50, 49, 48, 48, 53]], [[50, 49, 48, 48, 48]], [52, 53, 51] :: NoPartyIDs.members]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let repriceFrequency ← readOptional [50, 49, 48, 50, 48] tokens
  let repriceBehaviorType ← readOptional [50, 49, 48, 50, 49] tokens
  let mtpGroupID ← readOptional [50, 51, 54, 50] tokens
  let matchTradePrevention ← readOptional [50, 49, 48, 48, 49] tokens
  let riskGroupID ← readOptional [50, 49, 48, 48, 53] tokens
  let cancelGroupID ← readOptional [50, 49, 48, 48, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, orderQty, ordType, price, timeInForce, positionEffect, tradingCapacity, execInst, transactTime, repriceFrequency, repriceBehaviorType, mtpGroupID, matchTradePrevention, riskGroupID, cancelGroupID, noPartyIDs }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have repriceFrequency := readOptional_part [50, 49, 48, 50, 48] record.repriceFrequency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have repriceBehaviorType := readOptional_part [50, 49, 48, 50, 49] record.repriceBehaviorType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have mtpGroupID := readOptional_part [50, 51, 54, 50] record.mtpGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have matchTradePrevention := readOptional_part [50, 49, 48, 48, 49] record.matchTradePrevention tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have riskGroupID := readOptional_part [50, 49, 48, 48, 53] record.riskGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have cancelGroupID := readOptional_part [50, 49, 48, 48, 48] record.cancelGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, orderQty, ordType, price, timeInForce, positionEffect, tradingCapacity, execInst, transactTime, repriceFrequency, repriceBehaviorType, mtpGroupID, matchTradePrevention, riskGroupID, cancelGroupID, noPartyIDs, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  symbol : Option (Terminated 1)  -- tag 55
  maturityDate : Option (Terminated 1)  -- tag 541
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  transactTime : Terminated 1  -- tag 60

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [54, 48] record.transactTime]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[51, 55]], [[49, 49]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[54, 48]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { origClOrdID, orderID, clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, orderQty, ordType, price, transactTime }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, origClOrdID, orderID, clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, orderQty, ordType, price, transactTime, some_bind] <;> rfl

structure OrderCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  symbol : Option (Terminated 1)  -- tag 55
  maturityDate : Option (Terminated 1)  -- tag 541
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[51, 55]], [[49, 49]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[54, 48]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { origClOrdID, orderID, clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, transactTime }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, origClOrdID, orderID, clOrdID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, transactTime, some_bind] <;> rfl

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

structure NoAllocsAllocationInstruction where
  allocQty : Terminated 1  -- tag 80
  allocPositionEffect : Option (Terminated 1)  -- tag 1047
  tradingCapacity : Option (Terminated 1)  -- tag 1815
  noNestedPartyIDs : List NoNestedPartyIDs  -- tag 539

def NoAllocsAllocationInstruction.parts (record : NoAllocsAllocationInstruction) : List Part :=
  [Part.required [56, 48] record.allocQty,
   Part.optional [49, 48, 52, 55] record.allocPositionEffect,
   Part.optional [49, 56, 49, 53] record.tradingCapacity,
   Part.group [53, 51, 57] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within record.noNestedPartyIDs]

def NoAllocsAllocationInstruction.tags : List (List (List UInt8)) :=
  [[[56, 48]], [[49, 48, 52, 55]], [[49, 56, 49, 53]], [53, 51, 57] :: NoNestedPartyIDs.members]

theorem NoAllocsAllocationInstruction.shape (record : NoAllocsAllocationInstruction) : record.parts.map Part.tags = NoAllocsAllocationInstruction.tags := rfl

def NoAllocsAllocationInstruction.decode (tokens : List Token) : Option NoAllocsAllocationInstruction := do
  let allocQty ← readRequired [56, 48] tokens
  let allocPositionEffect ← readOptional [49, 48, 52, 55] tokens
  let tradingCapacity ← readOptional [49, 56, 49, 53] tokens
  let noNestedPartyIDs ← readGroup [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.decode tokens
  pure { allocQty, allocPositionEffect, tradingCapacity, noNestedPartyIDs }

theorem NoAllocsAllocationInstruction.decode_agrees (record : NoAllocsAllocationInstruction) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocsAllocationInstruction.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocsAllocationInstruction.decode tokens = some record := by
  have distinct : NoAllocsAllocationInstruction.tags.flatten.Nodup := by decide +kernel
  have allocQty := readRequired_part [56, 48] record.allocQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocPositionEffect := readOptional_part [49, 48, 52, 55] record.allocPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingCapacity := readOptional_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noNestedPartyIDs := readGroup_part [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within NoNestedPartyIDs.decode NoNestedPartyIDs.decode_encode NoNestedPartyIDs.led record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoAllocsAllocationInstruction.decode, allocQty, allocPositionEffect, tradingCapacity, noNestedPartyIDs, some_bind] <;> rfl

def NoAllocsAllocationInstruction.members : List (List UInt8) := NoAllocsAllocationInstruction.tags.flatten

def NoAllocsAllocationInstruction.encode (entry : NoAllocsAllocationInstruction) : List Token := encodeParts entry.parts

theorem NoAllocsAllocationInstruction.decode_encode (entry : NoAllocsAllocationInstruction) : NoAllocsAllocationInstruction.decode entry.encode = some entry :=
  NoAllocsAllocationInstruction.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAllocsAllocationInstruction.within (entry : NoAllocsAllocationInstruction) : ∀ token ∈ entry.encode, token.tag ∈ NoAllocsAllocationInstruction.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAllocsAllocationInstruction.shape] at this

theorem NoAllocsAllocationInstruction.led (entry : NoAllocsAllocationInstruction) : Lead [56, 48] entry.encode :=
  lead_parts [56, 48] entry.allocQty _ NoAllocsAllocationInstruction.tags.tail rfl (by decide +kernel)

structure AllocationInstruction where
  allocID : Terminated 1  -- tag 70
  allocType : Terminated 1  -- tag 626
  allocTransType : Terminated 1  -- tag 71
  refAllocID : Option (Terminated 1)  -- tag 72
  optionsSecurityID : Option (Terminated 1)  -- tag 21035
  symbol : Option (Terminated 1)  -- tag 55
  maturityDate : Option (Terminated 1)  -- tag 541
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Terminated 1  -- tag 54
  noExecs : List NoExecs  -- tag 124
  noAllocsAllocationInstruction : List NoAllocsAllocationInstruction  -- tag 78

def AllocationInstruction.parts (record : AllocationInstruction) : List Part :=
  [Part.required [55, 48] record.allocID,
   Part.required [54, 50, 54] record.allocType,
   Part.required [55, 49] record.allocTransType,
   Part.optional [55, 50] record.refAllocID,
   Part.optional [50, 49, 48, 51, 53] record.optionsSecurityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [53, 52] record.side,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.group [55, 56] NoAllocsAllocationInstruction.members NoAllocsAllocationInstruction.encode NoAllocsAllocationInstruction.within record.noAllocsAllocationInstruction]

def AllocationInstruction.tags : List (List (List UInt8)) :=
  [[[55, 48]], [[54, 50, 54]], [[55, 49]], [[55, 50]], [[50, 49, 48, 51, 53]], [[53, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [49, 50, 52] :: NoExecs.members, [55, 56] :: NoAllocsAllocationInstruction.members]

theorem AllocationInstruction.shape (record : AllocationInstruction) : record.parts.map Part.tags = AllocationInstruction.tags := rfl

def AllocationInstruction.decode (tokens : List Token) : Option AllocationInstruction := do
  let allocID ← readRequired [55, 48] tokens
  let allocType ← readRequired [54, 50, 54] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let refAllocID ← readOptional [55, 50] tokens
  let optionsSecurityID ← readOptional [50, 49, 48, 51, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readRequired [53, 52] tokens
  let noExecs ← readGroup [49, 50, 52] [49, 48, 48, 51] NoExecs.members NoExecs.decode tokens
  let noAllocsAllocationInstruction ← readGroup [55, 56] [56, 48] NoAllocsAllocationInstruction.members NoAllocsAllocationInstruction.decode tokens
  pure { allocID, allocType, allocTransType, refAllocID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, noExecs, noAllocsAllocationInstruction }

theorem AllocationInstruction.decode_agrees (record : AllocationInstruction) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationInstruction.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationInstruction.decode tokens = some record := by
  have distinct : AllocationInstruction.tags.flatten.Nodup := by decide +kernel
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocType := readRequired_part [54, 50, 54] record.allocType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refAllocID := readOptional_part [55, 50] record.refAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have optionsSecurityID := readOptional_part [50, 49, 48, 51, 53] record.optionsSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [49, 48, 48, 51] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noAllocsAllocationInstruction := readGroup_part [55, 56] [56, 48] NoAllocsAllocationInstruction.members NoAllocsAllocationInstruction.encode NoAllocsAllocationInstruction.within NoAllocsAllocationInstruction.decode NoAllocsAllocationInstruction.decode_encode NoAllocsAllocationInstruction.led record.noAllocsAllocationInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [AllocationInstruction.decode, allocID, allocType, allocTransType, refAllocID, optionsSecurityID, symbol, maturityDate, putOrCall, strikePrice, side, noExecs, noAllocsAllocationInstruction, some_bind] <;> rfl

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | allocationInstruction (header : Header) (r0 : AllocationInstruction)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationInstruction header r0 => ⟨[51, 53], ⟨[74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [74] then
        if known (Header.tags ++ AllocationInstruction.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationInstruction.decode rest
          pure (.allocationInstruction header r0)
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

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationInstruction (header : Header) (r0 : AllocationInstruction) :
    Message.decode (Message.tokens (.allocationInstruction header r0)) = some (.allocationInstruction header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstruction.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationInstruction.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationInstruction.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationInstruction.tags) rfl
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
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | allocationInstruction header r0 => exact Message.decode_allocationInstruction header r0

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

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_allocationInstruction (header : Header) (r0 : AllocationInstruction) :
    Message.decodeBytes (Message.encode (.allocationInstruction header r0)) = some (.allocationInstruction header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationInstruction.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationInstruction header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | allocationInstruction header r0 => exact Message.decodeBytes_allocationInstruction header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.MemxMemxoptionsOrderentryFixV110AClient
