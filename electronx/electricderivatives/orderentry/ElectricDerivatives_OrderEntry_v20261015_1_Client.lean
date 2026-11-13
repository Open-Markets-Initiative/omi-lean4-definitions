import Wire

/-!
# ElectronX Markets Order Entry v20261015.1, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.ElectronxElectricderivativesOrderentryFixV202610151Client

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, origSendingTime }

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
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, origSendingTime, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  password : Option (Terminated 1)  -- tag 554
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [53, 53, 52] record.password,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[53, 53, 52]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let password ← readOptional [53, 53, 52] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, password, defaultApplVerID }

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
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, password, defaultApplVerID, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  pure { refSeqNum, text, refTagID, refMsgType, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
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
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  custOrderCapacity : Terminated 1  -- tag 582
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  noPartyIDs : List NoPartyIDs  -- tag 453
  manualOrderIndicator : Terminated 1  -- tag 1028

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [53, 56, 50] record.custOrderCapacity,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[49, 49, 48]], [[49, 50, 54]], [[53, 56, 50]], [[53, 56, 51]], [52, 53, 51] :: NoPartyIDs.members, [[49, 48, 50, 56]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let custOrderCapacity ← readRequired [53, 56, 50] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, minQty, expireTime, custOrderCapacity, clOrdLinkID, noPartyIDs, manualOrderIndicator }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readRequired_part [49] record.account tokens
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
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have custOrderCapacity := readRequired_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, execInst, orderQty, ordType, price, side, symbol, timeInForce, minQty, expireTime, custOrderCapacity, clOrdLinkID, noPartyIDs, manualOrderIndicator, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  account : Option (Terminated 1)  -- tag 1
  execInst : Option (Terminated 1)  -- tag 18
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  ordType : Option (Terminated 1)  -- tag 40
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [49] record.account,
   Part.optional [49, 56] record.execInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.optional [52, 48] record.ordType,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[49]], [[49, 56]], [[53, 53]], [[53, 52]], [[52, 48]], [[51, 56]], [[52, 52]], [[53, 57]], [[49, 50, 54]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let account ← readOptional [49] tokens
  let execInst ← readOptional [49, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  pure { clOrdID, origClOrdID, account, execInst, symbol, side, ordType, orderQty, price, timeInForce, expireTime }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, clOrdID, origClOrdID, account, execInst, symbol, side, ordType, orderQty, price, timeInForce, expireTime, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  side : Option (Terminated 1)  -- tag 54
  price : Option (Terminated 1)  -- tag 44

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 52] record.side,
   Part.optional [52, 52] record.price]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[53, 53]], [[53, 52]], [[52, 52]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readOptional [53, 52] tokens
  let price ← readOptional [52, 52] tokens
  pure { clOrdID, origClOrdID, symbol, side, price }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, origClOrdID, symbol, side, price, some_bind] <;> rfl

structure OrderMassCancelRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityID : Option (Terminated 1)  -- tag 48
  symbol : Option (Terminated 1)  -- tag 55
  massCancelRequestType : Terminated 1  -- tag 530
  clOrdLinkID : Option (Terminated 1)  -- tag 583

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 53] record.symbol,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [53, 56, 51] record.clOrdLinkID]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[50, 50]], [[52, 56]], [[53, 53]], [[53, 51, 48]], [[53, 56, 51]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  pure { account, clOrdID, securityIDSource, securityID, symbol, massCancelRequestType, clOrdLinkID }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, account, clOrdID, securityIDSource, securityID, symbol, massCancelRequestType, clOrdLinkID, some_bind] <;> rfl

structure TradeCaptureReportRequest where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  startTime : Option (Terminated 1)  -- tag 9593
  endTime : Option (Terminated 1)  -- tag 9594

def TradeCaptureReportRequest.parts (record : TradeCaptureReportRequest) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [57, 53, 57, 51] record.startTime,
   Part.optional [57, 53, 57, 52] record.endTime]

def TradeCaptureReportRequest.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[50, 54, 51]], [[57, 53, 57, 51]], [[57, 53, 57, 52]]]

theorem TradeCaptureReportRequest.shape (record : TradeCaptureReportRequest) : record.parts.map Part.tags = TradeCaptureReportRequest.tags := rfl

def TradeCaptureReportRequest.decode (tokens : List Token) : Option TradeCaptureReportRequest := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let startTime ← readOptional [57, 53, 57, 51] tokens
  let endTime ← readOptional [57, 53, 57, 52] tokens
  pure { tradeRequestID, tradeRequestType, subscriptionRequestType, startTime, endTime }

theorem TradeCaptureReportRequest.decode_agrees (record : TradeCaptureReportRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportRequest.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have startTime := readOptional_part [57, 53, 57, 51] record.startTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have endTime := readOptional_part [57, 53, 57, 52] record.endTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReportRequest.decode, tradeRequestID, tradeRequestType, subscriptionRequestType, startTime, endTime, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | reject (header : Header) (r0 : Reject)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], ⟨[113], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequest header r0 => ⟨[51, 53], ⟨[65, 68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
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
      else if token.value.val = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
        else none
      else if token.value.val = [65, 68] then
        if known (Header.tags ++ TradeCaptureReportRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequest.decode rest
          pure (.tradeCaptureReportRequest header r0)
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

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
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

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decode (Message.tokens (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | reject header r0 => exact Message.decode_reject header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decode_tradeCaptureReportRequest header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

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

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[113], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

theorem Message.decodeBytes_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decodeBytes_tradeCaptureReportRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.ElectronxElectricderivativesOrderentryFixV202610151Client
