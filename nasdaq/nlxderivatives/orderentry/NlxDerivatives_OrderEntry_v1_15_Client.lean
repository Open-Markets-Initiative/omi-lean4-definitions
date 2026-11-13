import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v1.15, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNlxderivativesOrderentryFixV115Client

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, possResend, sendingTime, origSendingTime, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  heartBtInt : Terminated 1  -- tag 108
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 52, 49]], [[49, 48, 56]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, resetSeqNumFlag, heartBtInt, username, password, newPassword, defaultApplVerID }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, resetSeqNumFlag, heartBtInt, username, password, newPassword, defaultApplVerID, some_bind] <;> rfl

structure Logout where
  sessionStatus : Option (Terminated 1)  -- tag 1409
  text : Option (Terminated 1)  -- tag 58

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [53, 56] record.text]

def Logout.tags : List (List (List UInt8)) :=
  [[[49, 52, 48, 57]], [[53, 56]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let text ← readOptional [53, 56] tokens
  pure { sessionStatus, text }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, sessionStatus, text, some_bind] <;> rfl

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

structure UserRequest where
  userRequestID : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925

def UserRequest.parts (record : UserRequest) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [57, 50, 52] record.userRequestType,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword]

def UserRequest.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[57, 50, 52]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]]]

theorem UserRequest.shape (record : UserRequest) : record.parts.map Part.tags = UserRequest.tags := rfl

def UserRequest.decode (tokens : List Token) : Option UserRequest := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  pure { userRequestID, userRequestType, username, password, newPassword }

theorem UserRequest.decode_agrees (record : UserRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserRequest.decode tokens = some record := by
  have distinct : UserRequest.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [UserRequest.decode, userRequestID, userRequestType, username, password, newPassword, some_bind] <;> rfl

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
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  handlInst : Option (Terminated 1)  -- tag 21
  execInst : Option (Terminated 1)  -- tag 18
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  triggerType : Option (Terminated 1)  -- tag 1100
  triggerAction : Option (Terminated 1)  -- tag 1101
  triggerPrice : Option (Terminated 1)  -- tag 1102
  triggerSymbol : Option (Terminated 1)  -- tag 1103
  triggerSecurityID : Option (Terminated 1)  -- tag 1104
  triggerSecurityIDSource : Option (Terminated 1)  -- tag 1105
  triggerPriceType : Option (Terminated 1)  -- tag 1107
  triggerPriceDirection : Option (Terminated 1)  -- tag 1109
  timeInForce : Terminated 1  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  accountCode : Terminated 1  -- tag 20015
  allocID : Option (Terminated 1)  -- tag 70

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [50, 49] record.handlInst,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 49, 48, 48] record.triggerType,
   Part.optional [49, 49, 48, 49] record.triggerAction,
   Part.optional [49, 49, 48, 50] record.triggerPrice,
   Part.optional [49, 49, 48, 51] record.triggerSymbol,
   Part.optional [49, 49, 48, 52] record.triggerSecurityID,
   Part.optional [49, 49, 48, 53] record.triggerSecurityIDSource,
   Part.optional [49, 49, 48, 55] record.triggerPriceType,
   Part.optional [49, 49, 48, 57] record.triggerPriceDirection,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [50, 48, 48, 49, 53] record.accountCode,
   Part.optional [55, 48] record.allocID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[50, 49]], [[49, 56]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 48, 51]], [[49, 49, 48, 52]], [[49, 49, 48, 53]], [[49, 49, 48, 55]], [[49, 49, 48, 57]], [[53, 57]], [[52, 51, 50]], [[50, 48, 48, 49, 53]], [[55, 48]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let handlInst ← readOptional [50, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let triggerType ← readOptional [49, 49, 48, 48] tokens
  let triggerAction ← readOptional [49, 49, 48, 49] tokens
  let triggerPrice ← readOptional [49, 49, 48, 50] tokens
  let triggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let triggerSecurityID ← readOptional [49, 49, 48, 52] tokens
  let triggerSecurityIDSource ← readOptional [49, 49, 48, 53] tokens
  let triggerPriceType ← readOptional [49, 49, 48, 55] tokens
  let triggerPriceDirection ← readOptional [49, 49, 48, 57] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let accountCode ← readRequired [50, 48, 48, 49, 53] tokens
  let allocID ← readOptional [55, 48] tokens
  pure { clOrdID, noPartyIDs, account, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, expireDate, accountCode, allocID }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have triggerType := readOptional_part [49, 49, 48, 48] record.triggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have triggerAction := readOptional_part [49, 49, 48, 49] record.triggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have triggerPrice := readOptional_part [49, 49, 48, 50] record.triggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have triggerSymbol := readOptional_part [49, 49, 48, 51] record.triggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have triggerSecurityID := readOptional_part [49, 49, 48, 52] record.triggerSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have triggerSecurityIDSource := readOptional_part [49, 49, 48, 53] record.triggerSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have triggerPriceType := readOptional_part [49, 49, 48, 55] record.triggerPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have triggerPriceDirection := readOptional_part [49, 49, 48, 57] record.triggerPriceDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have accountCode := readRequired_part [50, 48, 48, 49, 53] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, noPartyIDs, account, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, expireDate, accountCode, allocID, some_bind] <;> rfl

structure OrderCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[51, 55]], [[49, 49]], [52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[54, 48]], [[51, 56]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  pure { origClOrdID, orderID, clOrdID, noPartyIDs, symbol, securityID, securityIDSource, side, transactTime, orderQty }

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
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, origClOrdID, orderID, clOrdID, noPartyIDs, symbol, securityID, securityIDSource, side, transactTime, orderQty, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  orderID : Option (Terminated 1)  -- tag 37
  noPartyIDs : List NoPartyIDs  -- tag 453
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  account : Option (Terminated 1)  -- tag 1
  allocID : Option (Terminated 1)  -- tag 70
  handlInst : Option (Terminated 1)  -- tag 21
  execInst : Option (Terminated 1)  -- tag 18
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  expireDate : Option (Terminated 1)  -- tag 432
  accountCode : Terminated 1  -- tag 20015

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49] record.account,
   Part.optional [55, 48] record.allocID,
   Part.optional [50, 49] record.handlInst,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [50, 48, 48, 49, 53] record.accountCode]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[52, 49]], [[49, 49]], [[49]], [[55, 48]], [[50, 49]], [[49, 56]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[52, 51, 50]], [[50, 48, 48, 49, 53]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let orderID ← readOptional [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let account ← readOptional [49] tokens
  let allocID ← readOptional [55, 48] tokens
  let handlInst ← readOptional [50, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let accountCode ← readRequired [50, 48, 48, 49, 53] tokens
  pure { orderID, noPartyIDs, origClOrdID, clOrdID, account, allocID, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, timeInForce, expireDate, accountCode }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have accountCode := readRequired_part [50, 48, 48, 49, 53] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, orderID, noPartyIDs, origClOrdID, clOrdID, account, allocID, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, timeInForce, expireDate, accountCode, some_bind] <;> rfl

structure NoSides where
  side : Terminated 1  -- tag 54
  orderID : Option (Terminated 1)  -- tag 37
  noPartyIDs : List NoPartyIDs  -- tag 453
  accountCode : Terminated 1  -- tag 20015
  transBkdTime : Option (Terminated 1)  -- tag 483
  account : Option (Terminated 1)  -- tag 1
  allocID : Option (Terminated 1)  -- tag 70
  aggressorIndicator : Option (Terminated 1)  -- tag 1057

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [50, 48, 48, 49, 53] record.accountCode,
   Part.optional [52, 56, 51] record.transBkdTime,
   Part.optional [49] record.account,
   Part.optional [55, 48] record.allocID,
   Part.optional [49, 48, 53, 55] record.aggressorIndicator]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[50, 48, 48, 49, 53]], [[52, 56, 51]], [[49]], [[55, 48]], [[49, 48, 53, 55]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let accountCode ← readRequired [50, 48, 48, 49, 53] tokens
  let transBkdTime ← readOptional [52, 56, 51] tokens
  let account ← readOptional [49] tokens
  let allocID ← readOptional [55, 48] tokens
  let aggressorIndicator ← readOptional [49, 48, 53, 55] tokens
  pure { side, orderID, noPartyIDs, accountCode, transBkdTime, account, allocID, aggressorIndicator }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have accountCode := readRequired_part [50, 48, 48, 49, 53] record.accountCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transBkdTime := readOptional_part [52, 56, 51] record.transBkdTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have aggressorIndicator := readOptional_part [49, 48, 53, 55] record.aggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [NoSides.decode, side, orderID, noPartyIDs, accountCode, transBkdTime, account, allocID, aggressorIndicator, some_bind] <;> rfl

def NoSides.members : List (List UInt8) := NoSides.tags.flatten

def NoSides.encode (entry : NoSides) : List Token := encodeParts entry.parts

theorem NoSides.decode_encode (entry : NoSides) : NoSides.decode entry.encode = some entry :=
  NoSides.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSides.within (entry : NoSides) : ∀ token ∈ entry.encode, token.tag ∈ NoSides.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSides.shape] at this

theorem NoSides.led (entry : NoSides) : Lead [53, 52] entry.encode :=
  lead_parts [53, 52] entry.side _ NoSides.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSource : Option (Terminated 1)  -- tag 603
  legLastPx : Option (Terminated 1)  -- tag 637
  legLastQty : Option (Terminated 1)  -- tag 1418
  noSides : List NoSides  -- tag 552
  legTrdMatchID : Option (Terminated 1)  -- tag 20200
  legSide : Option (Terminated 1)  -- tag 624
  legRatioQty : Option (Terminated 1)  -- tag 623

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSource,
   Part.optional [54, 51, 55] record.legLastPx,
   Part.optional [49, 52, 49, 56] record.legLastQty,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [50, 48, 50, 48, 48] record.legTrdMatchID,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [54, 50, 51] record.legRatioQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 51, 55]], [[49, 52, 49, 56]], [53, 53, 50] :: NoSides.members, [[50, 48, 50, 48, 48]], [[54, 50, 52]], [[54, 50, 51]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSource ← readOptional [54, 48, 51] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  let legLastQty ← readOptional [49, 52, 49, 56] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let legTrdMatchID ← readOptional [50, 48, 50, 48, 48] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, noSides, legTrdMatchID, legSide, legRatioQty }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSecurityID := readOptional_part [54, 48, 50] record.legSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSecurityIDSource := readOptional_part [54, 48, 51] record.legSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legLastPx := readOptional_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legLastQty := readOptional_part [49, 52, 49, 56] record.legLastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legTrdMatchID := readOptional_part [50, 48, 50, 48, 48] record.legTrdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, noSides, legTrdMatchID, legSide, legRatioQty, some_bind] <;> rfl

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

structure SecurityDefinitionRequest where
  securityReqID : Terminated 1  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  symbol : Terminated 1  -- tag 55
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.required [53, 53] record.symbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[53, 53]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityRequestType, symbol, noLegs }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, symbol, noLegs, some_bind] <;> rfl

structure NoQuoteEntries where
  quoteEntryID : Terminated 1  -- tag 299
  quoteEntryRejectReason : Option (Terminated 1)  -- tag 368
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  bidPx : Option (Terminated 1)  -- tag 132
  offerPx : Option (Terminated 1)  -- tag 133
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135

def NoQuoteEntries.parts (record : NoQuoteEntries) : List Part :=
  [Part.required [50, 57, 57] record.quoteEntryID,
   Part.optional [51, 54, 56] record.quoteEntryRejectReason,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize]

def NoQuoteEntries.tags : List (List (List UInt8)) :=
  [[[50, 57, 57]], [[51, 54, 56]], [[53, 53]], [[52, 56]], [[50, 50]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]]]

theorem NoQuoteEntries.shape (record : NoQuoteEntries) : record.parts.map Part.tags = NoQuoteEntries.tags := rfl

def NoQuoteEntries.decode (tokens : List Token) : Option NoQuoteEntries := do
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let quoteEntryRejectReason ← readOptional [51, 54, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  pure { quoteEntryID, quoteEntryRejectReason, symbol, securityID, securityIDSource, bidPx, offerPx, bidSize, offerSize }

theorem NoQuoteEntries.decode_agrees (record : NoQuoteEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteEntries.decode tokens = some record := by
  have distinct : NoQuoteEntries.tags.flatten.Nodup := by decide +kernel
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteEntryRejectReason := readOptional_part [51, 54, 56] record.quoteEntryRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoQuoteEntries.decode, quoteEntryID, quoteEntryRejectReason, symbol, securityID, securityIDSource, bidPx, offerPx, bidSize, offerSize, some_bind] <;> rfl

def NoQuoteEntries.members : List (List UInt8) := NoQuoteEntries.tags.flatten

def NoQuoteEntries.encode (entry : NoQuoteEntries) : List Token := encodeParts entry.parts

theorem NoQuoteEntries.decode_encode (entry : NoQuoteEntries) : NoQuoteEntries.decode entry.encode = some entry :=
  NoQuoteEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteEntries.within (entry : NoQuoteEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteEntries.shape] at this

theorem NoQuoteEntries.led (entry : NoQuoteEntries) : Lead [50, 57, 57] entry.encode :=
  lead_parts [50, 57, 57] entry.quoteEntryID _ NoQuoteEntries.tags.tail rfl (by decide +kernel)

structure NoQuoteSets where
  quoteSetID : Terminated 1  -- tag 302
  totNoQuoteEntries : Option (Terminated 1)  -- tag 304
  noQuoteEntries : List NoQuoteEntries  -- tag 295

def NoQuoteSets.parts (record : NoQuoteSets) : List Part :=
  [Part.required [51, 48, 50] record.quoteSetID,
   Part.optional [51, 48, 52] record.totNoQuoteEntries,
   Part.group [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within record.noQuoteEntries]

def NoQuoteSets.tags : List (List (List UInt8)) :=
  [[[51, 48, 50]], [[51, 48, 52]], [50, 57, 53] :: NoQuoteEntries.members]

theorem NoQuoteSets.shape (record : NoQuoteSets) : record.parts.map Part.tags = NoQuoteSets.tags := rfl

def NoQuoteSets.decode (tokens : List Token) : Option NoQuoteSets := do
  let quoteSetID ← readRequired [51, 48, 50] tokens
  let totNoQuoteEntries ← readOptional [51, 48, 52] tokens
  let noQuoteEntries ← readGroup [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.decode tokens
  pure { quoteSetID, totNoQuoteEntries, noQuoteEntries }

theorem NoQuoteSets.decode_agrees (record : NoQuoteSets) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteSets.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteSets.decode tokens = some record := by
  have distinct : NoQuoteSets.tags.flatten.Nodup := by decide +kernel
  have quoteSetID := readRequired_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have totNoQuoteEntries := readOptional_part [51, 48, 52] record.totNoQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noQuoteEntries := readGroup_part [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within NoQuoteEntries.decode NoQuoteEntries.decode_encode NoQuoteEntries.led record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoQuoteSets.decode, quoteSetID, totNoQuoteEntries, noQuoteEntries, some_bind] <;> rfl

def NoQuoteSets.members : List (List UInt8) := NoQuoteSets.tags.flatten

def NoQuoteSets.encode (entry : NoQuoteSets) : List Token := encodeParts entry.parts

theorem NoQuoteSets.decode_encode (entry : NoQuoteSets) : NoQuoteSets.decode entry.encode = some entry :=
  NoQuoteSets.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteSets.within (entry : NoQuoteSets) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteSets.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteSets.shape] at this

theorem NoQuoteSets.led (entry : NoQuoteSets) : Lead [51, 48, 50] entry.encode :=
  lead_parts [51, 48, 50] entry.quoteSetID _ NoQuoteSets.tags.tail rfl (by decide +kernel)

structure MassQuote where
  quoteID : Terminated 1  -- tag 117
  quoteType : Terminated 1  -- tag 537
  quoteResponseLevel : Terminated 1  -- tag 301
  defBidSize : Option (Terminated 1)  -- tag 293
  defOfferSize : Option (Terminated 1)  -- tag 294
  noQuoteSets : List NoQuoteSets  -- tag 296

def MassQuote.parts (record : MassQuote) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [53, 51, 55] record.quoteType,
   Part.required [51, 48, 49] record.quoteResponseLevel,
   Part.optional [50, 57, 51] record.defBidSize,
   Part.optional [50, 57, 52] record.defOfferSize,
   Part.group [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within record.noQuoteSets]

def MassQuote.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[53, 51, 55]], [[51, 48, 49]], [[50, 57, 51]], [[50, 57, 52]], [50, 57, 54] :: NoQuoteSets.members]

theorem MassQuote.shape (record : MassQuote) : record.parts.map Part.tags = MassQuote.tags := rfl

def MassQuote.decode (tokens : List Token) : Option MassQuote := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteType ← readRequired [53, 51, 55] tokens
  let quoteResponseLevel ← readRequired [51, 48, 49] tokens
  let defBidSize ← readOptional [50, 57, 51] tokens
  let defOfferSize ← readOptional [50, 57, 52] tokens
  let noQuoteSets ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.decode tokens
  pure { quoteID, quoteType, quoteResponseLevel, defBidSize, defOfferSize, noQuoteSets }

theorem MassQuote.decode_agrees (record : MassQuote) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuote.decode tokens = some record := by
  have distinct : MassQuote.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteType := readRequired_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteResponseLevel := readRequired_part [51, 48, 49] record.quoteResponseLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have defBidSize := readOptional_part [50, 57, 51] record.defBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defOfferSize := readOptional_part [50, 57, 52] record.defOfferSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noQuoteSets := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within NoQuoteSets.decode NoQuoteSets.decode_encode NoQuoteSets.led record.noQuoteSets tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [MassQuote.decode, quoteID, quoteType, quoteResponseLevel, defBidSize, defOfferSize, noQuoteSets, some_bind] <;> rfl

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  minQty : Option (Terminated 1)  -- tag 110

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [49, 49, 48] record.minQty]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[49, 49, 48]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  pure { symbol, securityID, securityIDSource, side, minQty }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, side, minQty, some_bind] <;> rfl

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure QuoteRequest where
  quoteReqID : Terminated 1  -- tag 131
  noRelatedSym : List NoRelatedSym  -- tag 146

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [49, 52, 54] :: NoRelatedSym.members]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { quoteReqID, noRelatedSym }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, noRelatedSym, some_bind] <;> rfl

structure MMProtectionSetLimit where
  underlyingSecurityID : Terminated 1  -- tag 309
  underlyingSymbol : Terminated 1  -- tag 311
  protectionRequestID : Terminated 1  -- tag 20114
  protectionQtyLimit : Terminated 1  -- tag 20110
  protectionDeltaLimit : Terminated 1  -- tag 20111
  protectionFrozenLimit : Terminated 1  -- tag 20112
  protectionExposureLimit : Terminated 1  -- tag 20113

def MMProtectionSetLimit.parts (record : MMProtectionSetLimit) : List Part :=
  [Part.required [51, 48, 57] record.underlyingSecurityID,
   Part.required [51, 49, 49] record.underlyingSymbol,
   Part.required [50, 48, 49, 49, 52] record.protectionRequestID,
   Part.required [50, 48, 49, 49, 48] record.protectionQtyLimit,
   Part.required [50, 48, 49, 49, 49] record.protectionDeltaLimit,
   Part.required [50, 48, 49, 49, 50] record.protectionFrozenLimit,
   Part.required [50, 48, 49, 49, 51] record.protectionExposureLimit]

def MMProtectionSetLimit.tags : List (List (List UInt8)) :=
  [[[51, 48, 57]], [[51, 49, 49]], [[50, 48, 49, 49, 52]], [[50, 48, 49, 49, 48]], [[50, 48, 49, 49, 49]], [[50, 48, 49, 49, 50]], [[50, 48, 49, 49, 51]]]

theorem MMProtectionSetLimit.shape (record : MMProtectionSetLimit) : record.parts.map Part.tags = MMProtectionSetLimit.tags := rfl

def MMProtectionSetLimit.decode (tokens : List Token) : Option MMProtectionSetLimit := do
  let underlyingSecurityID ← readRequired [51, 48, 57] tokens
  let underlyingSymbol ← readRequired [51, 49, 49] tokens
  let protectionRequestID ← readRequired [50, 48, 49, 49, 52] tokens
  let protectionQtyLimit ← readRequired [50, 48, 49, 49, 48] tokens
  let protectionDeltaLimit ← readRequired [50, 48, 49, 49, 49] tokens
  let protectionFrozenLimit ← readRequired [50, 48, 49, 49, 50] tokens
  let protectionExposureLimit ← readRequired [50, 48, 49, 49, 51] tokens
  pure { underlyingSecurityID, underlyingSymbol, protectionRequestID, protectionQtyLimit, protectionDeltaLimit, protectionFrozenLimit, protectionExposureLimit }

theorem MMProtectionSetLimit.decode_agrees (record : MMProtectionSetLimit) (tokens : List Token)
    (agrees : ∀ tags ∈ MMProtectionSetLimit.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MMProtectionSetLimit.decode tokens = some record := by
  have distinct : MMProtectionSetLimit.tags.flatten.Nodup := by decide +kernel
  have underlyingSecurityID := readRequired_part [51, 48, 57] record.underlyingSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have underlyingSymbol := readRequired_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have protectionRequestID := readRequired_part [50, 48, 49, 49, 52] record.protectionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have protectionQtyLimit := readRequired_part [50, 48, 49, 49, 48] record.protectionQtyLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have protectionDeltaLimit := readRequired_part [50, 48, 49, 49, 49] record.protectionDeltaLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have protectionFrozenLimit := readRequired_part [50, 48, 49, 49, 50] record.protectionFrozenLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have protectionExposureLimit := readRequired_part [50, 48, 49, 49, 51] record.protectionExposureLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [MMProtectionSetLimit.decode, underlyingSecurityID, underlyingSymbol, protectionRequestID, protectionQtyLimit, protectionDeltaLimit, protectionFrozenLimit, protectionExposureLimit, some_bind] <;> rfl

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  tradeReportTransType : Terminated 1  -- tag 487
  tradeReportType : Terminated 1  -- tag 856
  trdType : Terminated 1  -- tag 828
  previouslyReported : Terminated 1  -- tag 570
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  tradeDate : Terminated 1  -- tag 75
  transactTime : Terminated 1  -- tag 60
  futureReferencePrice : Option (Terminated 1)  -- tag 20016
  noSides : List NoSides  -- tag 552

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [56, 50, 56] record.trdType,
   Part.required [53, 55, 48] record.previouslyReported,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.required [55, 53] record.tradeDate,
   Part.required [54, 48] record.transactTime,
   Part.optional [50, 48, 48, 49, 54] record.futureReferencePrice,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[52, 56, 55]], [[56, 53, 54]], [[56, 50, 56]], [[53, 55, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [[51, 50]], [[51, 49]], [[55, 53]], [[54, 48]], [[50, 48, 48, 49, 54]], [53, 53, 50] :: NoSides.members]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let trdType ← readRequired [56, 50, 56] tokens
  let previouslyReported ← readRequired [53, 55, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let futureReferencePrice ← readOptional [50, 48, 48, 49, 54] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  pure { tradeReportID, tradeReportTransType, tradeReportType, trdType, previouslyReported, symbol, securityID, securityIDSource, lastQty, lastPx, tradeDate, transactTime, futureReferencePrice, noSides }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have previouslyReported := readRequired_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have futureReferencePrice := readOptional_part [50, 48, 48, 49, 54] record.futureReferencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, tradeReportTransType, tradeReportType, trdType, previouslyReported, symbol, securityID, securityIDSource, lastQty, lastPx, tradeDate, transactTime, futureReferencePrice, noSides, some_bind] <;> rfl

structure MultilegTradeReport where
  tradeReportID : Terminated 1  -- tag 571
  trdType : Terminated 1  -- tag 828
  noLegs : List NoLegs  -- tag 555
  transactTime : Terminated 1  -- tag 60

def MultilegTradeReport.parts (record : MultilegTradeReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.required [56, 50, 56] record.trdType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.required [54, 48] record.transactTime]

def MultilegTradeReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[56, 50, 56]], [53, 53, 53] :: NoLegs.members, [[54, 48]]]

theorem MultilegTradeReport.shape (record : MultilegTradeReport) : record.parts.map Part.tags = MultilegTradeReport.tags := rfl

def MultilegTradeReport.decode (tokens : List Token) : Option MultilegTradeReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let trdType ← readRequired [56, 50, 56] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { tradeReportID, trdType, noLegs, transactTime }

theorem MultilegTradeReport.decode_agrees (record : MultilegTradeReport) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegTradeReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegTradeReport.decode tokens = some record := by
  have distinct : MultilegTradeReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [MultilegTradeReport.decode, tradeReportID, trdType, noLegs, transactTime, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | userRequest (header : Header) (r0 : UserRequest)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | massQuote (header : Header) (r0 : MassQuote)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | mMProtectionSetLimit (header : Header) (r0 : MMProtectionSetLimit)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | multilegTradeReport (header : Header) (r0 : MultilegTradeReport)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userRequest header r0 => ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuote header r0 => ⟨[51, 53], ⟨[105], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .mMProtectionSetLimit header r0 => ⟨[51, 53], ⟨[77, 77], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegTradeReport header r0 => ⟨[51, 53], ⟨[85, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value.val = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
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
      else if token.value.val = [66, 69] then
        if known (Header.tags ++ UserRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserRequest.decode rest
          pure (.userRequest header r0)
        else none
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
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
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value.val = [105] then
        if known (Header.tags ++ MassQuote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuote.decode rest
          pure (.massQuote header r0)
        else none
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value.val = [77, 77] then
        if known (Header.tags ++ MMProtectionSetLimit.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MMProtectionSetLimit.decode rest
          pure (.mMProtectionSetLimit header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [85, 70] then
        if known (Header.tags ++ MultilegTradeReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MultilegTradeReport.decode rest
          pure (.multilegTradeReport header r0)
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

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
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

theorem Message.decode_userRequest (header : Header) (r0 : UserRequest) :
    Message.decode (Message.tokens (.userRequest header r0)) = some (.userRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags) rfl
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

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuote (header : Header) (r0 : MassQuote) :
    Message.decode (Message.tokens (.massQuote header r0)) = some (.massQuote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_mMProtectionSetLimit (header : Header) (r0 : MMProtectionSetLimit) :
    Message.decode (Message.tokens (.mMProtectionSetLimit header r0)) = some (.mMProtectionSetLimit header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionSetLimit.tags) rfl rfl (by decide +kernel))
  have c1 := MMProtectionSetLimit.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionSetLimit.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MMProtectionSetLimit.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_multilegTradeReport (header : Header) (r0 : MultilegTradeReport) :
    Message.decode (Message.tokens (.multilegTradeReport header r0)) = some (.multilegTradeReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MultilegTradeReport.tags) rfl rfl (by decide +kernel))
  have c1 := MultilegTradeReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MultilegTradeReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MultilegTradeReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | userRequest header r0 => exact Message.decode_userRequest header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | massQuote header r0 => exact Message.decode_massQuote header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | mMProtectionSetLimit header r0 => exact Message.decode_mMProtectionSetLimit header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | multilegTradeReport header r0 => exact Message.decode_multilegTradeReport header r0

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

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[50], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

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

theorem Message.decodeBytes_userRequest (header : Header) (r0 : UserRequest) :
    Message.decodeBytes (Message.encode (.userRequest header r0)) = some (.userRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userRequest header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

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

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_massQuote (header : Header) (r0 : MassQuote) :
    Message.decodeBytes (Message.encode (.massQuote header r0)) = some (.massQuote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[105], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MassQuote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuote header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_mMProtectionSetLimit (header : Header) (r0 : MMProtectionSetLimit) :
    Message.decodeBytes (Message.encode (.mMProtectionSetLimit header r0)) = some (.mMProtectionSetLimit header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[77, 77], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MMProtectionSetLimit.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_mMProtectionSetLimit header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_multilegTradeReport (header : Header) (r0 : MultilegTradeReport) :
    Message.decodeBytes (Message.encode (.multilegTradeReport header r0)) = some (.multilegTradeReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MultilegTradeReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_multilegTradeReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | userRequest header r0 => exact Message.decodeBytes_userRequest header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | massQuote header r0 => exact Message.decodeBytes_massQuote header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | mMProtectionSetLimit header r0 => exact Message.decodeBytes_mMProtectionSetLimit header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | multilegTradeReport header r0 => exact Message.decodeBytes_multilegTradeReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNlxderivativesOrderentryFixV115Client
