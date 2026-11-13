import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v2.08, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNordicderivativesOrderentryFixV208Client

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
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier }

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
  have partyRoleQualifier := readOptional_part [50, 51, 55, 54] record.partyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, partyRoleQualifier, some_bind] <;> rfl

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

structure NoTradingSessions where
  tradingSessionID : Terminated 1  -- tag 336

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]]]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { tradingSessionID }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, some_bind] <;> rfl

def NoTradingSessions.members : List (List UInt8) := NoTradingSessions.tags.flatten

def NoTradingSessions.encode (entry : NoTradingSessions) : List Token := encodeParts entry.parts

theorem NoTradingSessions.decode_encode (entry : NoTradingSessions) : NoTradingSessions.decode entry.encode = some entry :=
  NoTradingSessions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradingSessions.within (entry : NoTradingSessions) : ∀ token ∈ entry.encode, token.tag ∈ NoTradingSessions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradingSessions.shape] at this

theorem NoTradingSessions.led (entry : NoTradingSessions) : Lead [51, 51, 54] entry.encode :=
  lead_parts [51, 51, 54] entry.tradingSessionID _ NoTradingSessions.tags.tail rfl (by decide +kernel)

structure NoOrderAttributes where
  orderAttributeType : Terminated 1  -- tag 2594
  orderAttributeValue : Terminated 1  -- tag 2595

def NoOrderAttributes.parts (record : NoOrderAttributes) : List Part :=
  [Part.required [50, 53, 57, 52] record.orderAttributeType,
   Part.required [50, 53, 57, 53] record.orderAttributeValue]

def NoOrderAttributes.tags : List (List (List UInt8)) :=
  [[[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem NoOrderAttributes.shape (record : NoOrderAttributes) : record.parts.map Part.tags = NoOrderAttributes.tags := rfl

def NoOrderAttributes.decode (tokens : List Token) : Option NoOrderAttributes := do
  let orderAttributeType ← readRequired [50, 53, 57, 52] tokens
  let orderAttributeValue ← readRequired [50, 53, 57, 53] tokens
  pure { orderAttributeType, orderAttributeValue }

theorem NoOrderAttributes.decode_agrees (record : NoOrderAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderAttributes.decode tokens = some record := by
  have distinct : NoOrderAttributes.tags.flatten.Nodup := by decide +kernel
  have orderAttributeType := readRequired_part [50, 53, 57, 52] record.orderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderAttributeValue := readRequired_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoOrderAttributes.decode, orderAttributeType, orderAttributeValue, some_bind] <;> rfl

def NoOrderAttributes.members : List (List UInt8) := NoOrderAttributes.tags.flatten

def NoOrderAttributes.encode (entry : NoOrderAttributes) : List Token := encodeParts entry.parts

theorem NoOrderAttributes.decode_encode (entry : NoOrderAttributes) : NoOrderAttributes.decode entry.encode = some entry :=
  NoOrderAttributes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrderAttributes.within (entry : NoOrderAttributes) : ∀ token ∈ entry.encode, token.tag ∈ NoOrderAttributes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrderAttributes.shape] at this

theorem NoOrderAttributes.led (entry : NoOrderAttributes) : Lead [50, 53, 57, 52] entry.encode :=
  lead_parts [50, 53, 57, 52] entry.orderAttributeType _ NoOrderAttributes.tags.tail rfl (by decide +kernel)

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  maxFloor : Option (Terminated 1)  -- tag 111
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
  triggerTradingSessionID : Option (Terminated 1)  -- tag 1113
  triggerSymbol : Option (Terminated 1)  -- tag 1103
  triggerSecurityID : Option (Terminated 1)  -- tag 1104
  triggerSecurityIDSource : Option (Terminated 1)  -- tag 1105
  triggerPriceType : Option (Terminated 1)  -- tag 1107
  triggerPriceDirection : Option (Terminated 1)  -- tag 1109
  timeInForce : Terminated 1  -- tag 59
  noTradingSessions : List NoTradingSessions  -- tag 386
  expireDate : Option (Terminated 1)  -- tag 432
  orderCapacity : Terminated 1  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  allocID : Option (Terminated 1)  -- tag 70
  matchIncrement : Option (Terminated 1)  -- tag 1089
  orderReference : Option (Terminated 1)  -- tag 20009
  selfMatchPreventionID : Option (Terminated 1)  -- tag 20015

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [49, 49, 49] record.maxFloor,
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
   Part.optional [49, 49, 49, 51] record.triggerTradingSessionID,
   Part.optional [49, 49, 48, 51] record.triggerSymbol,
   Part.optional [49, 49, 48, 52] record.triggerSecurityID,
   Part.optional [49, 49, 48, 53] record.triggerSecurityIDSource,
   Part.optional [49, 49, 48, 55] record.triggerPriceType,
   Part.optional [49, 49, 48, 57] record.triggerPriceDirection,
   Part.required [53, 57] record.timeInForce,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [55, 48] record.allocID,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [50, 48, 48, 48, 57] record.orderReference,
   Part.optional [50, 48, 48, 49, 53] record.selfMatchPreventionID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[49, 49, 49]], [[50, 49]], [[49, 56]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 49, 51]], [[49, 49, 48, 51]], [[49, 49, 48, 52]], [[49, 49, 48, 53]], [[49, 49, 48, 55]], [[49, 49, 48, 57]], [[53, 57]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 50]], [[53, 50, 56]], [[53, 50, 57]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[55, 48]], [[49, 48, 56, 57]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 53]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
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
  let triggerTradingSessionID ← readOptional [49, 49, 49, 51] tokens
  let triggerSymbol ← readOptional [49, 49, 48, 51] tokens
  let triggerSecurityID ← readOptional [49, 49, 48, 52] tokens
  let triggerSecurityIDSource ← readOptional [49, 49, 48, 53] tokens
  let triggerPriceType ← readOptional [49, 49, 48, 55] tokens
  let triggerPriceDirection ← readOptional [49, 49, 48, 57] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let allocID ← readOptional [55, 48] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let orderReference ← readOptional [50, 48, 48, 48, 57] tokens
  let selfMatchPreventionID ← readOptional [50, 48, 48, 49, 53] tokens
  pure { clOrdID, noPartyIDs, account, maxFloor, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerTradingSessionID, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, noTradingSessions, expireDate, orderCapacity, orderRestrictions, noOrderAttributes, allocID, matchIncrement, orderReference, selfMatchPreventionID }

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
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have triggerType := readOptional_part [49, 49, 48, 48] record.triggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have triggerAction := readOptional_part [49, 49, 48, 49] record.triggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have triggerPrice := readOptional_part [49, 49, 48, 50] record.triggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have triggerTradingSessionID := readOptional_part [49, 49, 49, 51] record.triggerTradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have triggerSymbol := readOptional_part [49, 49, 48, 51] record.triggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have triggerSecurityID := readOptional_part [49, 49, 48, 52] record.triggerSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have triggerSecurityIDSource := readOptional_part [49, 49, 48, 53] record.triggerSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have triggerPriceType := readOptional_part [49, 49, 48, 55] record.triggerPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have triggerPriceDirection := readOptional_part [49, 49, 48, 57] record.triggerPriceDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderReference := readOptional_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 48, 48, 49, 53] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, noPartyIDs, account, maxFloor, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerTradingSessionID, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, noTradingSessions, expireDate, orderCapacity, orderRestrictions, noOrderAttributes, allocID, matchIncrement, orderReference, selfMatchPreventionID, some_bind] <;> rfl

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
  maxFloor : Option (Terminated 1)  -- tag 111
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
  noTradingSessions : List NoTradingSessions  -- tag 386
  expireDate : Option (Terminated 1)  -- tag 432
  orderCapacity : Terminated 1  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  orderReference : Option (Terminated 1)  -- tag 20009
  selfMatchPreventionID : Option (Terminated 1)  -- tag 20015

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49] record.account,
   Part.optional [55, 48] record.allocID,
   Part.optional [49, 49, 49] record.maxFloor,
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
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.optional [50, 48, 48, 48, 57] record.orderReference,
   Part.optional [50, 48, 48, 49, 53] record.selfMatchPreventionID]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[52, 49]], [[49, 49]], [[49]], [[55, 48]], [[49, 49, 49]], [[50, 49]], [[49, 56]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[54, 48]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 50]], [[53, 50, 56]], [[53, 50, 57]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 53]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let orderID ← readOptional [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let account ← readOptional [49] tokens
  let allocID ← readOptional [55, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
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
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let orderReference ← readOptional [50, 48, 48, 48, 57] tokens
  let selfMatchPreventionID ← readOptional [50, 48, 48, 49, 53] tokens
  pure { orderID, noPartyIDs, origClOrdID, clOrdID, account, allocID, maxFloor, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, timeInForce, noTradingSessions, expireDate, orderCapacity, orderRestrictions, orderReference, selfMatchPreventionID }

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
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderReference := readOptional_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 48, 48, 49, 53] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, orderID, noPartyIDs, origClOrdID, clOrdID, account, allocID, maxFloor, handlInst, execInst, symbol, securityID, securityIDSource, side, transactTime, orderQty, ordType, price, timeInForce, noTradingSessions, expireDate, orderCapacity, orderRestrictions, orderReference, selfMatchPreventionID, some_bind] <;> rfl

structure NoEvents where
  eventType : Terminated 1  -- tag 865
  eventDate : Terminated 1  -- tag 866

def NoEvents.parts (record : NoEvents) : List Part :=
  [Part.required [56, 54, 53] record.eventType,
   Part.required [56, 54, 54] record.eventDate]

def NoEvents.tags : List (List (List UInt8)) :=
  [[[56, 54, 53]], [[56, 54, 54]]]

theorem NoEvents.shape (record : NoEvents) : record.parts.map Part.tags = NoEvents.tags := rfl

def NoEvents.decode (tokens : List Token) : Option NoEvents := do
  let eventType ← readRequired [56, 54, 53] tokens
  let eventDate ← readRequired [56, 54, 54] tokens
  pure { eventType, eventDate }

theorem NoEvents.decode_agrees (record : NoEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEvents.decode tokens = some record := by
  have distinct : NoEvents.tags.flatten.Nodup := by decide +kernel
  have eventType := readRequired_part [56, 54, 53] record.eventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventDate := readRequired_part [56, 54, 54] record.eventDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoEvents.decode, eventType, eventDate, some_bind] <;> rfl

def NoEvents.members : List (List UInt8) := NoEvents.tags.flatten

def NoEvents.encode (entry : NoEvents) : List Token := encodeParts entry.parts

theorem NoEvents.decode_encode (entry : NoEvents) : NoEvents.decode entry.encode = some entry :=
  NoEvents.decode_agrees entry _ (fun _ _ => rfl)

theorem NoEvents.within (entry : NoEvents) : ∀ token ∈ entry.encode, token.tag ∈ NoEvents.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoEvents.shape] at this

theorem NoEvents.led (entry : NoEvents) : Lead [56, 54, 53] entry.encode :=
  lead_parts [56, 54, 53] entry.eventType _ NoEvents.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityID : Option (Terminated 1)  -- tag 602
  legSecurityIDSource : Option (Terminated 1)  -- tag 603
  legLastPx : Option (Terminated 1)  -- tag 637
  legLastQty : Option (Terminated 1)  -- tag 1418
  legNumber : Option (Terminated 1)  -- tag 1152
  legSide : Option (Terminated 1)  -- tag 624
  legRatioQty : Option (Terminated 1)  -- tag 623

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 50] record.legSecurityID,
   Part.optional [54, 48, 51] record.legSecurityIDSource,
   Part.optional [54, 51, 55] record.legLastPx,
   Part.optional [49, 52, 49, 56] record.legLastQty,
   Part.optional [49, 49, 53, 50] record.legNumber,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [54, 50, 51] record.legRatioQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 48, 50]], [[54, 48, 51]], [[54, 51, 55]], [[49, 52, 49, 56]], [[49, 49, 53, 50]], [[54, 50, 52]], [[54, 50, 51]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityID ← readOptional [54, 48, 50] tokens
  let legSecurityIDSource ← readOptional [54, 48, 51] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  let legLastQty ← readOptional [49, 52, 49, 56] tokens
  let legNumber ← readOptional [49, 49, 53, 50] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  pure { legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, legNumber, legSide, legRatioQty }

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
  have legNumber := readOptional_part [49, 49, 53, 50] record.legNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityID, legSecurityIDSource, legLastPx, legLastQty, legNumber, legSide, legRatioQty, some_bind] <;> rfl

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
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noEvents : List NoEvents  -- tag 864
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[53, 53]], [[52, 56]], [[50, 50]], [56, 54, 52] :: NoEvents.members, [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityRequestType, symbol, securityID, securityIDSource, noEvents, noLegs }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, symbol, securityID, securityIDSource, noEvents, noLegs, some_bind] <;> rfl

structure NoRootPartyIDs where
  rootPartyID : Terminated 1  -- tag 1117
  rootPartyIDSource : Terminated 1  -- tag 1118
  rootPartyRole : Terminated 1  -- tag 1119
  rootPartyRoleQualifier : Option (Terminated 1)  -- tag 2388

def NoRootPartyIDs.parts (record : NoRootPartyIDs) : List Part :=
  [Part.required [49, 49, 49, 55] record.rootPartyID,
   Part.required [49, 49, 49, 56] record.rootPartyIDSource,
   Part.required [49, 49, 49, 57] record.rootPartyRole,
   Part.optional [50, 51, 56, 56] record.rootPartyRoleQualifier]

def NoRootPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 49, 49, 55]], [[49, 49, 49, 56]], [[49, 49, 49, 57]], [[50, 51, 56, 56]]]

theorem NoRootPartyIDs.shape (record : NoRootPartyIDs) : record.parts.map Part.tags = NoRootPartyIDs.tags := rfl

def NoRootPartyIDs.decode (tokens : List Token) : Option NoRootPartyIDs := do
  let rootPartyID ← readRequired [49, 49, 49, 55] tokens
  let rootPartyIDSource ← readRequired [49, 49, 49, 56] tokens
  let rootPartyRole ← readRequired [49, 49, 49, 57] tokens
  let rootPartyRoleQualifier ← readOptional [50, 51, 56, 56] tokens
  pure { rootPartyID, rootPartyIDSource, rootPartyRole, rootPartyRoleQualifier }

theorem NoRootPartyIDs.decode_agrees (record : NoRootPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRootPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRootPartyIDs.decode tokens = some record := by
  have distinct : NoRootPartyIDs.tags.flatten.Nodup := by decide +kernel
  have rootPartyID := readRequired_part [49, 49, 49, 55] record.rootPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rootPartyIDSource := readRequired_part [49, 49, 49, 56] record.rootPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rootPartyRole := readRequired_part [49, 49, 49, 57] record.rootPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rootPartyRoleQualifier := readOptional_part [50, 51, 56, 56] record.rootPartyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoRootPartyIDs.decode, rootPartyID, rootPartyIDSource, rootPartyRole, rootPartyRoleQualifier, some_bind] <;> rfl

def NoRootPartyIDs.members : List (List UInt8) := NoRootPartyIDs.tags.flatten

def NoRootPartyIDs.encode (entry : NoRootPartyIDs) : List Token := encodeParts entry.parts

theorem NoRootPartyIDs.decode_encode (entry : NoRootPartyIDs) : NoRootPartyIDs.decode entry.encode = some entry :=
  NoRootPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRootPartyIDs.within (entry : NoRootPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRootPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRootPartyIDs.shape] at this

theorem NoRootPartyIDs.led (entry : NoRootPartyIDs) : Lead [49, 49, 49, 55] entry.encode :=
  lead_parts [49, 49, 49, 55] entry.rootPartyID _ NoRootPartyIDs.tags.tail rfl (by decide +kernel)

structure NoOrders where
  clOrdID : Terminated 1  -- tag 11
  listSeqNo : Terminated 1  -- tag 67
  matchIncrement : Option (Terminated 1)  -- tag 1089
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Terminated 1  -- tag 59
  noTradingSessions : List NoTradingSessions  -- tag 386
  orderCapacity : Terminated 1  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderReference : Option (Terminated 1)  -- tag 20009

def NoOrders.parts (record : NoOrders) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [54, 55] record.listSeqNo,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 57] record.timeInForce,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [50, 48, 48, 48, 57] record.orderReference]

def NoOrders.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[54, 55]], [[49, 48, 56, 57]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [51, 56, 54] :: NoTradingSessions.members, [[53, 50, 56]], [[53, 50, 57]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[50, 48, 48, 48, 57]]]

theorem NoOrders.shape (record : NoOrders) : record.parts.map Part.tags = NoOrders.tags := rfl

def NoOrders.decode (tokens : List Token) : Option NoOrders := do
  let clOrdID ← readRequired [49, 49] tokens
  let listSeqNo ← readRequired [54, 55] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderReference ← readOptional [50, 48, 48, 48, 57] tokens
  pure { clOrdID, listSeqNo, matchIncrement, symbol, securityID, securityIDSource, side, orderQty, ordType, price, timeInForce, noTradingSessions, orderCapacity, orderRestrictions, noOrderAttributes, orderReference }

theorem NoOrders.decode_agrees (record : NoOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrders.decode tokens = some record := by
  have distinct : NoOrders.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have listSeqNo := readRequired_part [54, 55] record.listSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
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
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderReference := readOptional_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NoOrders.decode, clOrdID, listSeqNo, matchIncrement, symbol, securityID, securityIDSource, side, orderQty, ordType, price, timeInForce, noTradingSessions, orderCapacity, orderRestrictions, noOrderAttributes, orderReference, some_bind] <;> rfl

def NoOrders.members : List (List UInt8) := NoOrders.tags.flatten

def NoOrders.encode (entry : NoOrders) : List Token := encodeParts entry.parts

theorem NoOrders.decode_encode (entry : NoOrders) : NoOrders.decode entry.encode = some entry :=
  NoOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrders.within (entry : NoOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrders.shape] at this

theorem NoOrders.led (entry : NoOrders) : Lead [49, 49] entry.encode :=
  lead_parts [49, 49] entry.clOrdID _ NoOrders.tags.tail rfl (by decide +kernel)

structure NewOrderList where
  listID : Terminated 1  -- tag 66
  bidType : Terminated 1  -- tag 394
  contingencyType : Terminated 1  -- tag 1385
  totNoOrders : Terminated 1  -- tag 68
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  noOrders : List NoOrders  -- tag 73

def NewOrderList.parts (record : NewOrderList) : List Part :=
  [Part.required [54, 54] record.listID,
   Part.required [51, 57, 52] record.bidType,
   Part.required [49, 51, 56, 53] record.contingencyType,
   Part.required [54, 56] record.totNoOrders,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.group [55, 51] NoOrders.members NoOrders.encode NoOrders.within record.noOrders]

def NewOrderList.tags : List (List (List UInt8)) :=
  [[[54, 54]], [[51, 57, 52]], [[49, 51, 56, 53]], [[54, 56]], [49, 49, 49, 54] :: NoRootPartyIDs.members, [55, 51] :: NoOrders.members]

theorem NewOrderList.shape (record : NewOrderList) : record.parts.map Part.tags = NewOrderList.tags := rfl

def NewOrderList.decode (tokens : List Token) : Option NewOrderList := do
  let listID ← readRequired [54, 54] tokens
  let bidType ← readRequired [51, 57, 52] tokens
  let contingencyType ← readRequired [49, 51, 56, 53] tokens
  let totNoOrders ← readRequired [54, 56] tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let noOrders ← readGroup [55, 51] [49, 49] NoOrders.members NoOrders.decode tokens
  pure { listID, bidType, contingencyType, totNoOrders, noRootPartyIDs, noOrders }

theorem NewOrderList.decode_agrees (record : NewOrderList) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderList.decode tokens = some record := by
  have distinct : NewOrderList.tags.flatten.Nodup := by decide +kernel
  have listID := readRequired_part [54, 54] record.listID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bidType := readRequired_part [51, 57, 52] record.bidType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contingencyType := readRequired_part [49, 51, 56, 53] record.contingencyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have totNoOrders := readRequired_part [54, 56] record.totNoOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noOrders := readGroup_part [55, 51] [49, 49] NoOrders.members NoOrders.encode NoOrders.within NoOrders.decode NoOrders.decode_encode NoOrders.led record.noOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NewOrderList.decode, listID, bidType, contingencyType, totNoOrders, noRootPartyIDs, noOrders, some_bind] <;> rfl

structure ListCancelRequest where
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  listID : Terminated 1  -- tag 66
  transactTime : Terminated 1  -- tag 60

def ListCancelRequest.parts (record : ListCancelRequest) : List Part :=
  [Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.required [54, 54] record.listID,
   Part.required [54, 48] record.transactTime]

def ListCancelRequest.tags : List (List (List UInt8)) :=
  [[49, 49, 49, 54] :: NoRootPartyIDs.members, [[54, 54]], [[54, 48]]]

theorem ListCancelRequest.shape (record : ListCancelRequest) : record.parts.map Part.tags = ListCancelRequest.tags := rfl

def ListCancelRequest.decode (tokens : List Token) : Option ListCancelRequest := do
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let listID ← readRequired [54, 54] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { noRootPartyIDs, listID, transactTime }

theorem ListCancelRequest.decode_agrees (record : ListCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ ListCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ListCancelRequest.decode tokens = some record := by
  have distinct : ListCancelRequest.tags.flatten.Nodup := by decide +kernel
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have listID := readRequired_part [54, 54] record.listID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ListCancelRequest.decode, noRootPartyIDs, listID, transactTime, some_bind] <;> rfl

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
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  noQuoteSets : List NoQuoteSets  -- tag 296

def MassQuote.parts (record : MassQuote) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [53, 51, 55] record.quoteType,
   Part.required [51, 48, 49] record.quoteResponseLevel,
   Part.optional [50, 57, 51] record.defBidSize,
   Part.optional [50, 57, 52] record.defOfferSize,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.group [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within record.noQuoteSets]

def MassQuote.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[53, 51, 55]], [[51, 48, 49]], [[50, 57, 51]], [[50, 57, 52]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [50, 57, 54] :: NoQuoteSets.members]

theorem MassQuote.shape (record : MassQuote) : record.parts.map Part.tags = MassQuote.tags := rfl

def MassQuote.decode (tokens : List Token) : Option MassQuote := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteType ← readRequired [53, 51, 55] tokens
  let quoteResponseLevel ← readRequired [51, 48, 49] tokens
  let defBidSize ← readOptional [50, 57, 51] tokens
  let defOfferSize ← readOptional [50, 57, 52] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let noQuoteSets ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.decode tokens
  pure { quoteID, quoteType, quoteResponseLevel, defBidSize, defOfferSize, noPartyIDs, account, noQuoteSets }

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
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noQuoteSets := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within NoQuoteSets.decode NoQuoteSets.decode_encode NoQuoteSets.led record.noQuoteSets tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [MassQuote.decode, quoteID, quoteType, quoteResponseLevel, defBidSize, defOfferSize, noPartyIDs, account, noQuoteSets, some_bind] <;> rfl

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  minQty : Option (Terminated 1)  -- tag 110

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [49, 49, 48] record.minQty]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[49, 49, 48]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
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
  have securityID := readRequired_part [52, 56] record.securityID tokens
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

structure OneSidedAuctionRequest where
  auctionRequestID : Terminated 1  -- tag 20001
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  auctionType : Terminated 1  -- tag 20002
  quantityLimit : Option (Terminated 1)  -- tag 20010
  referencePrice : Option (Terminated 1)  -- tag 20011
  bookTransparency : Terminated 1  -- tag 20003
  settlDate : Option (Terminated 1)  -- tag 64
  settlPrice : Option (Terminated 1)  -- tag 730
  auctionUncrossTime : Terminated 1  -- tag 20004

def OneSidedAuctionRequest.parts (record : OneSidedAuctionRequest) : List Part :=
  [Part.required [50, 48, 48, 48, 49] record.auctionRequestID,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [50, 48, 48, 48, 50] record.auctionType,
   Part.optional [50, 48, 48, 49, 48] record.quantityLimit,
   Part.optional [50, 48, 48, 49, 49] record.referencePrice,
   Part.required [50, 48, 48, 48, 51] record.bookTransparency,
   Part.optional [54, 52] record.settlDate,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.required [50, 48, 48, 48, 52] record.auctionUncrossTime]

def OneSidedAuctionRequest.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 48, 49]], [[53, 53]], [[52, 56]], [[50, 50]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 49, 49]], [[50, 48, 48, 48, 51]], [[54, 52]], [[55, 51, 48]], [[50, 48, 48, 48, 52]]]

theorem OneSidedAuctionRequest.shape (record : OneSidedAuctionRequest) : record.parts.map Part.tags = OneSidedAuctionRequest.tags := rfl

def OneSidedAuctionRequest.decode (tokens : List Token) : Option OneSidedAuctionRequest := do
  let auctionRequestID ← readRequired [50, 48, 48, 48, 49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let auctionType ← readRequired [50, 48, 48, 48, 50] tokens
  let quantityLimit ← readOptional [50, 48, 48, 49, 48] tokens
  let referencePrice ← readOptional [50, 48, 48, 49, 49] tokens
  let bookTransparency ← readRequired [50, 48, 48, 48, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let auctionUncrossTime ← readRequired [50, 48, 48, 48, 52] tokens
  pure { auctionRequestID, symbol, securityID, securityIDSource, auctionType, quantityLimit, referencePrice, bookTransparency, settlDate, settlPrice, auctionUncrossTime }

theorem OneSidedAuctionRequest.decode_agrees (record : OneSidedAuctionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OneSidedAuctionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OneSidedAuctionRequest.decode tokens = some record := by
  have distinct : OneSidedAuctionRequest.tags.flatten.Nodup := by decide +kernel
  have auctionRequestID := readRequired_part [50, 48, 48, 48, 49] record.auctionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have auctionType := readRequired_part [50, 48, 48, 48, 50] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quantityLimit := readOptional_part [50, 48, 48, 49, 48] record.quantityLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have referencePrice := readOptional_part [50, 48, 48, 49, 49] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have bookTransparency := readRequired_part [50, 48, 48, 48, 51] record.bookTransparency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have auctionUncrossTime := readRequired_part [50, 48, 48, 48, 52] record.auctionUncrossTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [OneSidedAuctionRequest.decode, auctionRequestID, symbol, securityID, securityIDSource, auctionType, quantityLimit, referencePrice, bookTransparency, settlDate, settlPrice, auctionUncrossTime, some_bind] <;> rfl

structure OneSidedCancelAuctionRequest where
  auctionRequestID : Terminated 1  -- tag 20001
  origAuctionRequestID : Terminated 1  -- tag 20012
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def OneSidedCancelAuctionRequest.parts (record : OneSidedCancelAuctionRequest) : List Part :=
  [Part.required [50, 48, 48, 48, 49] record.auctionRequestID,
   Part.required [50, 48, 48, 49, 50] record.origAuctionRequestID,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def OneSidedCancelAuctionRequest.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 48, 49]], [[50, 48, 48, 49, 50]], [[53, 53]], [[52, 56]], [[50, 50]]]

theorem OneSidedCancelAuctionRequest.shape (record : OneSidedCancelAuctionRequest) : record.parts.map Part.tags = OneSidedCancelAuctionRequest.tags := rfl

def OneSidedCancelAuctionRequest.decode (tokens : List Token) : Option OneSidedCancelAuctionRequest := do
  let auctionRequestID ← readRequired [50, 48, 48, 48, 49] tokens
  let origAuctionRequestID ← readRequired [50, 48, 48, 49, 50] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { auctionRequestID, origAuctionRequestID, symbol, securityID, securityIDSource }

theorem OneSidedCancelAuctionRequest.decode_agrees (record : OneSidedCancelAuctionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OneSidedCancelAuctionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OneSidedCancelAuctionRequest.decode tokens = some record := by
  have distinct : OneSidedCancelAuctionRequest.tags.flatten.Nodup := by decide +kernel
  have auctionRequestID := readRequired_part [50, 48, 48, 48, 49] record.auctionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origAuctionRequestID := readRequired_part [50, 48, 48, 49, 50] record.origAuctionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [OneSidedCancelAuctionRequest.decode, auctionRequestID, origAuctionRequestID, symbol, securityID, securityIDSource, some_bind] <;> rfl

structure NoRelatedInstruments where
  relatedInstrumentType : Terminated 1  -- tag 1648
  relatedSymbol : Option (Terminated 1)  -- tag 1649
  relatedSecurityID : Option (Terminated 1)  -- tag 1650
  relatedSecurityIDSource : Option (Terminated 1)  -- tag 1651

def NoRelatedInstruments.parts (record : NoRelatedInstruments) : List Part :=
  [Part.required [49, 54, 52, 56] record.relatedInstrumentType,
   Part.optional [49, 54, 52, 57] record.relatedSymbol,
   Part.optional [49, 54, 53, 48] record.relatedSecurityID,
   Part.optional [49, 54, 53, 49] record.relatedSecurityIDSource]

def NoRelatedInstruments.tags : List (List (List UInt8)) :=
  [[[49, 54, 52, 56]], [[49, 54, 52, 57]], [[49, 54, 53, 48]], [[49, 54, 53, 49]]]

theorem NoRelatedInstruments.shape (record : NoRelatedInstruments) : record.parts.map Part.tags = NoRelatedInstruments.tags := rfl

def NoRelatedInstruments.decode (tokens : List Token) : Option NoRelatedInstruments := do
  let relatedInstrumentType ← readRequired [49, 54, 52, 56] tokens
  let relatedSymbol ← readOptional [49, 54, 52, 57] tokens
  let relatedSecurityID ← readOptional [49, 54, 53, 48] tokens
  let relatedSecurityIDSource ← readOptional [49, 54, 53, 49] tokens
  pure { relatedInstrumentType, relatedSymbol, relatedSecurityID, relatedSecurityIDSource }

theorem NoRelatedInstruments.decode_agrees (record : NoRelatedInstruments) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedInstruments.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedInstruments.decode tokens = some record := by
  have distinct : NoRelatedInstruments.tags.flatten.Nodup := by decide +kernel
  have relatedInstrumentType := readRequired_part [49, 54, 52, 56] record.relatedInstrumentType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have relatedSymbol := readOptional_part [49, 54, 52, 57] record.relatedSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have relatedSecurityID := readOptional_part [49, 54, 53, 48] record.relatedSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have relatedSecurityIDSource := readOptional_part [49, 54, 53, 49] record.relatedSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoRelatedInstruments.decode, relatedInstrumentType, relatedSymbol, relatedSecurityID, relatedSecurityIDSource, some_bind] <;> rfl

def NoRelatedInstruments.members : List (List UInt8) := NoRelatedInstruments.tags.flatten

def NoRelatedInstruments.encode (entry : NoRelatedInstruments) : List Token := encodeParts entry.parts

theorem NoRelatedInstruments.decode_encode (entry : NoRelatedInstruments) : NoRelatedInstruments.decode entry.encode = some entry :=
  NoRelatedInstruments.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedInstruments.within (entry : NoRelatedInstruments) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedInstruments.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedInstruments.shape] at this

theorem NoRelatedInstruments.led (entry : NoRelatedInstruments) : Lead [49, 54, 52, 56] entry.encode :=
  lead_parts [49, 54, 52, 56] entry.relatedInstrumentType _ NoRelatedInstruments.tags.tail rfl (by decide +kernel)

structure NoNested2PartyIDs where
  nested2PartyID : Terminated 1  -- tag 757
  nested2PartyIDSource : Option (Terminated 1)  -- tag 758
  nested2PartyRole : Option (Terminated 1)  -- tag 759

def NoNested2PartyIDs.parts (record : NoNested2PartyIDs) : List Part :=
  [Part.required [55, 53, 55] record.nested2PartyID,
   Part.optional [55, 53, 56] record.nested2PartyIDSource,
   Part.optional [55, 53, 57] record.nested2PartyRole]

def NoNested2PartyIDs.tags : List (List (List UInt8)) :=
  [[[55, 53, 55]], [[55, 53, 56]], [[55, 53, 57]]]

theorem NoNested2PartyIDs.shape (record : NoNested2PartyIDs) : record.parts.map Part.tags = NoNested2PartyIDs.tags := rfl

def NoNested2PartyIDs.decode (tokens : List Token) : Option NoNested2PartyIDs := do
  let nested2PartyID ← readRequired [55, 53, 55] tokens
  let nested2PartyIDSource ← readOptional [55, 53, 56] tokens
  let nested2PartyRole ← readOptional [55, 53, 57] tokens
  pure { nested2PartyID, nested2PartyIDSource, nested2PartyRole }

theorem NoNested2PartyIDs.decode_agrees (record : NoNested2PartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoNested2PartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoNested2PartyIDs.decode tokens = some record := by
  have distinct : NoNested2PartyIDs.tags.flatten.Nodup := by decide +kernel
  have nested2PartyID := readRequired_part [55, 53, 55] record.nested2PartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have nested2PartyIDSource := readOptional_part [55, 53, 56] record.nested2PartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nested2PartyRole := readOptional_part [55, 53, 57] record.nested2PartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoNested2PartyIDs.decode, nested2PartyID, nested2PartyIDSource, nested2PartyRole, some_bind] <;> rfl

def NoNested2PartyIDs.members : List (List UInt8) := NoNested2PartyIDs.tags.flatten

def NoNested2PartyIDs.encode (entry : NoNested2PartyIDs) : List Token := encodeParts entry.parts

theorem NoNested2PartyIDs.decode_encode (entry : NoNested2PartyIDs) : NoNested2PartyIDs.decode entry.encode = some entry :=
  NoNested2PartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoNested2PartyIDs.within (entry : NoNested2PartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoNested2PartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoNested2PartyIDs.shape] at this

theorem NoNested2PartyIDs.led (entry : NoNested2PartyIDs) : Lead [55, 53, 55] entry.encode :=
  lead_parts [55, 53, 55] entry.nested2PartyID _ NoNested2PartyIDs.tags.tail rfl (by decide +kernel)

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

structure NoAllocs where
  allocAccount : Terminated 1  -- tag 79
  noNested2PartyIDs : List NoNested2PartyIDs  -- tag 756
  individualAllocID : Option (Terminated 1)  -- tag 467
  allocQty : Option (Terminated 1)  -- tag 80
  noNestedPartyIDs : List NoNestedPartyIDs  -- tag 539
  allocText : Option (Terminated 1)  -- tag 161
  commission : Option (Terminated 1)  -- tag 12
  commType : Option (Terminated 1)  -- tag 13
  externalTradeFeeType : Option (Terminated 1)  -- tag 20014
  allocPositionEffect : Option (Terminated 1)  -- tag 1047

def NoAllocs.parts (record : NoAllocs) : List Part :=
  [Part.required [55, 57] record.allocAccount,
   Part.group [55, 53, 54] NoNested2PartyIDs.members NoNested2PartyIDs.encode NoNested2PartyIDs.within record.noNested2PartyIDs,
   Part.optional [52, 54, 55] record.individualAllocID,
   Part.optional [56, 48] record.allocQty,
   Part.group [53, 51, 57] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within record.noNestedPartyIDs,
   Part.optional [49, 54, 49] record.allocText,
   Part.optional [49, 50] record.commission,
   Part.optional [49, 51] record.commType,
   Part.optional [50, 48, 48, 49, 52] record.externalTradeFeeType,
   Part.optional [49, 48, 52, 55] record.allocPositionEffect]

def NoAllocs.tags : List (List (List UInt8)) :=
  [[[55, 57]], [55, 53, 54] :: NoNested2PartyIDs.members, [[52, 54, 55]], [[56, 48]], [53, 51, 57] :: NoNestedPartyIDs.members, [[49, 54, 49]], [[49, 50]], [[49, 51]], [[50, 48, 48, 49, 52]], [[49, 48, 52, 55]]]

theorem NoAllocs.shape (record : NoAllocs) : record.parts.map Part.tags = NoAllocs.tags := rfl

def NoAllocs.decode (tokens : List Token) : Option NoAllocs := do
  let allocAccount ← readRequired [55, 57] tokens
  let noNested2PartyIDs ← readGroup [55, 53, 54] [55, 53, 55] NoNested2PartyIDs.members NoNested2PartyIDs.decode tokens
  let individualAllocID ← readOptional [52, 54, 55] tokens
  let allocQty ← readOptional [56, 48] tokens
  let noNestedPartyIDs ← readGroup [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.decode tokens
  let allocText ← readOptional [49, 54, 49] tokens
  let commission ← readOptional [49, 50] tokens
  let commType ← readOptional [49, 51] tokens
  let externalTradeFeeType ← readOptional [50, 48, 48, 49, 52] tokens
  let allocPositionEffect ← readOptional [49, 48, 52, 55] tokens
  pure { allocAccount, noNested2PartyIDs, individualAllocID, allocQty, noNestedPartyIDs, allocText, commission, commType, externalTradeFeeType, allocPositionEffect }

theorem NoAllocs.decode_agrees (record : NoAllocs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocs.decode tokens = some record := by
  have distinct : NoAllocs.tags.flatten.Nodup := by decide +kernel
  have allocAccount := readRequired_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noNested2PartyIDs := readGroup_part [55, 53, 54] [55, 53, 55] NoNested2PartyIDs.members NoNested2PartyIDs.encode NoNested2PartyIDs.within NoNested2PartyIDs.decode NoNested2PartyIDs.decode_encode NoNested2PartyIDs.led record.noNested2PartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have individualAllocID := readOptional_part [52, 54, 55] record.individualAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocQty := readOptional_part [56, 48] record.allocQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noNestedPartyIDs := readGroup_part [53, 51, 57] [53, 50, 52] NoNestedPartyIDs.members NoNestedPartyIDs.encode NoNestedPartyIDs.within NoNestedPartyIDs.decode NoNestedPartyIDs.decode_encode NoNestedPartyIDs.led record.noNestedPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocText := readOptional_part [49, 54, 49] record.allocText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have commType := readOptional_part [49, 51] record.commType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have externalTradeFeeType := readOptional_part [50, 48, 48, 49, 52] record.externalTradeFeeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have allocPositionEffect := readOptional_part [49, 48, 52, 55] record.allocPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoAllocs.decode, allocAccount, noNested2PartyIDs, individualAllocID, allocQty, noNestedPartyIDs, allocText, commission, commType, externalTradeFeeType, allocPositionEffect, some_bind] <;> rfl

def NoAllocs.members : List (List UInt8) := NoAllocs.tags.flatten

def NoAllocs.encode (entry : NoAllocs) : List Token := encodeParts entry.parts

theorem NoAllocs.decode_encode (entry : NoAllocs) : NoAllocs.decode entry.encode = some entry :=
  NoAllocs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAllocs.within (entry : NoAllocs) : ∀ token ∈ entry.encode, token.tag ∈ NoAllocs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAllocs.shape] at this

theorem NoAllocs.led (entry : NoAllocs) : Lead [55, 57] entry.encode :=
  lead_parts [55, 57] entry.allocAccount _ NoAllocs.tags.tail rfl (by decide +kernel)

structure NoSides where
  side : Terminated 1  -- tag 54
  orderID : Option (Terminated 1)  -- tag 37
  sideTradeID : Option (Terminated 1)  -- tag 1506
  strategyLinkID : Option (Terminated 1)  -- tag 1851
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  allocID : Option (Terminated 1)  -- tag 70
  aggressorIndicator : Option (Terminated 1)  -- tag 1057
  leavesQty : Option (Terminated 1)  -- tag 151
  orderCapacity : Option (Terminated 1)  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724
  transBkdTime : Option (Terminated 1)  -- tag 483
  cleanPrice : Option (Terminated 1)  -- tag 20006
  orderReference : Option (Terminated 1)  -- tag 20009
  positionEffect : Option (Terminated 1)  -- tag 77
  tradeAllocIndicator : Option (Terminated 1)  -- tag 826
  noAllocs : List NoAllocs  -- tag 78

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 53, 48, 54] record.sideTradeID,
   Part.optional [49, 56, 53, 49] record.strategyLinkID,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [55, 48] record.allocID,
   Part.optional [49, 48, 53, 55] record.aggressorIndicator,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [52, 56, 51] record.transBkdTime,
   Part.optional [50, 48, 48, 48, 54] record.cleanPrice,
   Part.optional [50, 48, 48, 48, 57] record.orderReference,
   Part.optional [55, 55] record.positionEffect,
   Part.optional [56, 50, 54] record.tradeAllocIndicator,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[51, 55]], [[49, 53, 48, 54]], [[49, 56, 53, 49]], [[54, 50, 53]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[55, 48]], [[49, 48, 53, 55]], [[49, 53, 49]], [[53, 50, 56]], [[53, 50, 57]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]], [[52, 56, 51]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 57]], [[55, 55]], [[56, 50, 54]], [55, 56] :: NoAllocs.members]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let sideTradeID ← readOptional [49, 53, 48, 54] tokens
  let strategyLinkID ← readOptional [49, 56, 53, 49] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let allocID ← readOptional [55, 48] tokens
  let aggressorIndicator ← readOptional [49, 48, 53, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let transBkdTime ← readOptional [52, 56, 51] tokens
  let cleanPrice ← readOptional [50, 48, 48, 48, 54] tokens
  let orderReference ← readOptional [50, 48, 48, 48, 57] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let tradeAllocIndicator ← readOptional [56, 50, 54] tokens
  let noAllocs ← readGroup [55, 56] [55, 57] NoAllocs.members NoAllocs.decode tokens
  pure { side, orderID, sideTradeID, strategyLinkID, tradingSessionSubID, noPartyIDs, account, allocID, aggressorIndicator, leavesQty, orderCapacity, orderRestrictions, noOrderAttributes, orderOrigination, transBkdTime, cleanPrice, orderReference, positionEffect, tradeAllocIndicator, noAllocs }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sideTradeID := readOptional_part [49, 53, 48, 54] record.sideTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have strategyLinkID := readOptional_part [49, 56, 53, 49] record.strategyLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have aggressorIndicator := readOptional_part [49, 48, 53, 55] record.aggressorIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have transBkdTime := readOptional_part [52, 56, 51] record.transBkdTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have cleanPrice := readOptional_part [50, 48, 48, 48, 54] record.cleanPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderReference := readOptional_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have tradeAllocIndicator := readOptional_part [56, 50, 54] record.tradeAllocIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [55, 57] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [NoSides.decode, side, orderID, sideTradeID, strategyLinkID, tradingSessionSubID, noPartyIDs, account, allocID, aggressorIndicator, leavesQty, orderCapacity, orderRestrictions, noOrderAttributes, orderOrigination, transBkdTime, cleanPrice, orderReference, positionEffect, tradeAllocIndicator, noAllocs, some_bind] <;> rfl

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

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  dealID : Option (Terminated 1)  -- tag 21000
  tradeReportRefID : Option (Terminated 1)  -- tag 572
  secondaryTradeReportRefID : Option (Terminated 1)  -- tag 881
  tradeReportTransType : Terminated 1  -- tag 487
  tradeReportType : Terminated 1  -- tag 856
  tradeHandlingInstr : Option (Terminated 1)  -- tag 1123
  offBookType : Option (Terminated 1)  -- tag 20202
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  previouslyReported : Option (Terminated 1)  -- tag 570
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  symbol : Option (Terminated 1)  -- tag 55
  noLegs : List NoLegs  -- tag 555
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noRelatedInstruments : List NoRelatedInstruments  -- tag 1647
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  tradeID : Option (Terminated 1)  -- tag 1003
  settlDate : Option (Terminated 1)  -- tag 64
  noSides : List NoSides  -- tag 552
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [50, 49, 48, 48, 48] record.dealID,
   Part.optional [53, 55, 50] record.tradeReportRefID,
   Part.optional [56, 56, 49] record.secondaryTradeReportRefID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.optional [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [50, 48, 50, 48, 50] record.offBookType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [53, 55, 48] record.previouslyReported,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.optional [53, 53] record.symbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [49, 54, 52, 55] NoRelatedInstruments.members NoRelatedInstruments.encode NoRelatedInstruments.within record.noRelatedInstruments,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [54, 52] record.settlDate,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[50, 49, 48, 48, 48]], [[53, 55, 50]], [[56, 56, 49]], [[52, 56, 55]], [[56, 53, 54]], [[49, 49, 50, 51]], [[50, 48, 50, 48, 50]], [[56, 50, 57]], [[56, 53, 53]], [[53, 55, 48]], [49, 49, 49, 54] :: NoRootPartyIDs.members, [[53, 53]], [53, 53, 53] :: NoLegs.members, [[52, 56]], [[50, 50]], [49, 54, 52, 55] :: NoRelatedInstruments.members, [[51, 50]], [[51, 49]], [[55, 53]], [[54, 48]], [[49, 48, 48, 51]], [[54, 52]], [53, 53, 50] :: NoSides.members, [[49, 51, 57, 48]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let dealID ← readOptional [50, 49, 48, 48, 48] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  let secondaryTradeReportRefID ← readOptional [56, 56, 49] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeHandlingInstr ← readOptional [49, 49, 50, 51] tokens
  let offBookType ← readOptional [50, 48, 50, 48, 50] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let previouslyReported ← readOptional [53, 55, 48] tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let symbol ← readOptional [53, 53] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noRelatedInstruments ← readGroup [49, 54, 52, 55] [49, 54, 52, 56] NoRelatedInstruments.members NoRelatedInstruments.decode tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  pure { tradeReportID, dealID, tradeReportRefID, secondaryTradeReportRefID, tradeReportTransType, tradeReportType, tradeHandlingInstr, offBookType, trdSubType, secondaryTrdType, previouslyReported, noRootPartyIDs, symbol, noLegs, securityID, securityIDSource, noRelatedInstruments, lastQty, lastPx, tradeDate, transactTime, tradeID, settlDate, noSides, tradePublishIndicator }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have dealID := readOptional_part [50, 49, 48, 48, 48] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have secondaryTradeReportRefID := readOptional_part [56, 56, 49] record.secondaryTradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradeHandlingInstr := readOptional_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have offBookType := readOptional_part [50, 48, 50, 48, 50] record.offBookType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have previouslyReported := readOptional_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noRelatedInstruments := readGroup_part [49, 54, 52, 55] [49, 54, 52, 56] NoRelatedInstruments.members NoRelatedInstruments.encode NoRelatedInstruments.within NoRelatedInstruments.decode NoRelatedInstruments.decode_encode NoRelatedInstruments.led record.noRelatedInstruments tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, dealID, tradeReportRefID, secondaryTradeReportRefID, tradeReportTransType, tradeReportType, tradeHandlingInstr, offBookType, trdSubType, secondaryTrdType, previouslyReported, noRootPartyIDs, symbol, noLegs, securityID, securityIDSource, noRelatedInstruments, lastQty, lastPx, tradeDate, transactTime, tradeID, settlDate, noSides, tradePublishIndicator, some_bind] <;> rfl

structure NoExecs where
  lastQty : Terminated 1  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  tradeID : Terminated 1  -- tag 1003

def NoExecs.parts (record : NoExecs) : List Part :=
  [Part.required [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 48, 48, 51] record.tradeID]

def NoExecs.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]], [[49, 48, 48, 51]]]

theorem NoExecs.shape (record : NoExecs) : record.parts.map Part.tags = NoExecs.tags := rfl

def NoExecs.decode (tokens : List Token) : Option NoExecs := do
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  pure { lastQty, lastPx, tradeID }

theorem NoExecs.decode_agrees (record : NoExecs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoExecs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoExecs.decode tokens = some record := by
  have distinct : NoExecs.tags.flatten.Nodup := by decide +kernel
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoExecs.decode, lastQty, lastPx, tradeID, some_bind] <;> rfl

def NoExecs.members : List (List UInt8) := NoExecs.tags.flatten

def NoExecs.encode (entry : NoExecs) : List Token := encodeParts entry.parts

theorem NoExecs.decode_encode (entry : NoExecs) : NoExecs.decode entry.encode = some entry :=
  NoExecs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoExecs.within (entry : NoExecs) : ∀ token ∈ entry.encode, token.tag ∈ NoExecs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoExecs.shape] at this

theorem NoExecs.led (entry : NoExecs) : Lead [51, 50] entry.encode :=
  lead_parts [51, 50] entry.lastQty _ NoExecs.tags.tail rfl (by decide +kernel)

structure AllocationInstruction where
  allocID : Terminated 1  -- tag 70
  allocTransType : Terminated 1  -- tag 71
  allocType : Terminated 1  -- tag 626
  noExecs : List NoExecs  -- tag 124
  side : Terminated 1  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  quantity : Terminated 1  -- tag 53
  tradeDate : Option (Terminated 1)  -- tag 75
  noAllocs : List NoAllocs  -- tag 78
  text : Option (Terminated 1)  -- tag 58

def AllocationInstruction.parts (record : AllocationInstruction) : List Part :=
  [Part.required [55, 48] record.allocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [54, 50, 54] record.allocType,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.required [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 51] record.quantity,
   Part.optional [55, 53] record.tradeDate,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs,
   Part.optional [53, 56] record.text]

def AllocationInstruction.tags : List (List (List UInt8)) :=
  [[[55, 48]], [[55, 49]], [[54, 50, 54]], [49, 50, 52] :: NoExecs.members, [[53, 52]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 51]], [[55, 53]], [55, 56] :: NoAllocs.members, [[53, 56]]]

theorem AllocationInstruction.shape (record : AllocationInstruction) : record.parts.map Part.tags = AllocationInstruction.tags := rfl

def AllocationInstruction.decode (tokens : List Token) : Option AllocationInstruction := do
  let allocID ← readRequired [55, 48] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let allocType ← readRequired [54, 50, 54] tokens
  let noExecs ← readGroup [49, 50, 52] [51, 50] NoExecs.members NoExecs.decode tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let quantity ← readRequired [53, 51] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let noAllocs ← readGroup [55, 56] [55, 57] NoAllocs.members NoAllocs.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { allocID, allocTransType, allocType, noExecs, side, symbol, securityID, securityIDSource, quantity, tradeDate, noAllocs, text }

theorem AllocationInstruction.decode_agrees (record : AllocationInstruction) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationInstruction.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationInstruction.decode tokens = some record := by
  have distinct : AllocationInstruction.tags.flatten.Nodup := by decide +kernel
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocType := readRequired_part [54, 50, 54] record.allocType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [51, 50] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have quantity := readRequired_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [55, 57] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [AllocationInstruction.decode, allocID, allocTransType, allocType, noExecs, side, symbol, securityID, securityIDSource, quantity, tradeDate, noAllocs, text, some_bind] <;> rfl

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
  | newOrderList (header : Header) (r0 : NewOrderList)
  | listCancelRequest (header : Header) (r0 : ListCancelRequest)
  | massQuote (header : Header) (r0 : MassQuote)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | oneSidedAuctionRequest (header : Header) (r0 : OneSidedAuctionRequest)
  | oneSidedCancelAuctionRequest (header : Header) (r0 : OneSidedCancelAuctionRequest)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | allocationInstruction (header : Header) (r0 : AllocationInstruction)

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
  | .newOrderList header r0 => ⟨[51, 53], ⟨[69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .listCancelRequest header r0 => ⟨[51, 53], ⟨[75], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuote header r0 => ⟨[51, 53], ⟨[105], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .oneSidedAuctionRequest header r0 => ⟨[51, 53], ⟨[85, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .oneSidedCancelAuctionRequest header r0 => ⟨[51, 53], ⟨[85, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationInstruction header r0 => ⟨[51, 53], ⟨[74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [69] then
        if known (Header.tags ++ NewOrderList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderList.decode rest
          pure (.newOrderList header r0)
        else none
      else if token.value.val = [75] then
        if known (Header.tags ++ ListCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ListCancelRequest.decode rest
          pure (.listCancelRequest header r0)
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
      else if token.value.val = [85, 66] then
        if known (Header.tags ++ OneSidedAuctionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OneSidedAuctionRequest.decode rest
          pure (.oneSidedAuctionRequest header r0)
        else none
      else if token.value.val = [85, 67] then
        if known (Header.tags ++ OneSidedCancelAuctionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OneSidedCancelAuctionRequest.decode rest
          pure (.oneSidedCancelAuctionRequest header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [74] then
        if known (Header.tags ++ AllocationInstruction.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationInstruction.decode rest
          pure (.allocationInstruction header r0)
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

theorem Message.decode_newOrderList (header : Header) (r0 : NewOrderList) :
    Message.decode (Message.tokens (.newOrderList header r0)) = some (.newOrderList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderList.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_listCancelRequest (header : Header) (r0 : ListCancelRequest) :
    Message.decode (Message.tokens (.listCancelRequest header r0)) = some (.listCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ListCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ListCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ListCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ListCancelRequest.tags) rfl
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

theorem Message.decode_oneSidedAuctionRequest (header : Header) (r0 : OneSidedAuctionRequest) :
    Message.decode (Message.tokens (.oneSidedAuctionRequest header r0)) = some (.oneSidedAuctionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedAuctionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OneSidedAuctionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedAuctionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OneSidedAuctionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_oneSidedCancelAuctionRequest (header : Header) (r0 : OneSidedCancelAuctionRequest) :
    Message.decode (Message.tokens (.oneSidedCancelAuctionRequest header r0)) = some (.oneSidedCancelAuctionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedCancelAuctionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OneSidedCancelAuctionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedCancelAuctionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OneSidedCancelAuctionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
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
  | newOrderList header r0 => exact Message.decode_newOrderList header r0
  | listCancelRequest header r0 => exact Message.decode_listCancelRequest header r0
  | massQuote header r0 => exact Message.decode_massQuote header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | oneSidedAuctionRequest header r0 => exact Message.decode_oneSidedAuctionRequest header r0
  | oneSidedCancelAuctionRequest header r0 => exact Message.decode_oneSidedCancelAuctionRequest header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | allocationInstruction header r0 => exact Message.decode_allocationInstruction header r0

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

theorem Message.decodeBytes_newOrderList (header : Header) (r0 : NewOrderList) :
    Message.decodeBytes (Message.encode (.newOrderList header r0)) = some (.newOrderList header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderList.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderList header r0

theorem Message.decodeBytes_listCancelRequest (header : Header) (r0 : ListCancelRequest) :
    Message.decodeBytes (Message.encode (.listCancelRequest header r0)) = some (.listCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[75], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ListCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_listCancelRequest header r0

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

theorem Message.decodeBytes_oneSidedAuctionRequest (header : Header) (r0 : OneSidedAuctionRequest) :
    Message.decodeBytes (Message.encode (.oneSidedAuctionRequest header r0)) = some (.oneSidedAuctionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OneSidedAuctionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oneSidedAuctionRequest header r0

theorem Message.decodeBytes_oneSidedCancelAuctionRequest (header : Header) (r0 : OneSidedCancelAuctionRequest) :
    Message.decodeBytes (Message.encode (.oneSidedCancelAuctionRequest header r0)) = some (.oneSidedCancelAuctionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OneSidedCancelAuctionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oneSidedCancelAuctionRequest header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_allocationInstruction (header : Header) (r0 : AllocationInstruction) :
    Message.decodeBytes (Message.encode (.allocationInstruction header r0)) = some (.allocationInstruction header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationInstruction.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationInstruction header r0

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
  | newOrderList header r0 => exact Message.decodeBytes_newOrderList header r0
  | listCancelRequest header r0 => exact Message.decodeBytes_listCancelRequest header r0
  | massQuote header r0 => exact Message.decodeBytes_massQuote header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | oneSidedAuctionRequest header r0 => exact Message.decodeBytes_oneSidedAuctionRequest header r0
  | oneSidedCancelAuctionRequest header r0 => exact Message.decodeBytes_oneSidedCancelAuctionRequest header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | allocationInstruction header r0 => exact Message.decodeBytes_allocationInstruction header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNordicderivativesOrderentryFixV208Client
