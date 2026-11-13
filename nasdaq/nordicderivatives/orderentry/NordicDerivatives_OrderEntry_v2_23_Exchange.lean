import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v2.23, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNordicderivativesOrderentryFixV223Exchange

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
  sessionStatus : Terminated 1  -- tag 1409
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.required [49, 52, 48, 57] record.sessionStatus,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 52, 49]], [[49, 48, 56]], [[49, 52, 48, 57]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let sessionStatus ← readRequired [49, 52, 48, 57] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, resetSeqNumFlag, heartBtInt, sessionStatus, defaultApplVerID }

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
  have sessionStatus := readRequired_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, resetSeqNumFlag, heartBtInt, sessionStatus, defaultApplVerID, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Terminated 1  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.required [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
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
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

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

structure UserResponse where
  userRequestID : Terminated 1  -- tag 923
  username : Terminated 1  -- tag 553
  userStatus : Terminated 1  -- tag 926
  userStatusText : Option (Terminated 1)  -- tag 927

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [53, 53, 51] record.username,
   Part.required [57, 50, 54] record.userStatus,
   Part.optional [57, 50, 55] record.userStatusText]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[53, 53, 51]], [[57, 50, 54]], [[57, 50, 55]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let username ← readRequired [53, 53, 51] tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  let userStatusText ← readOptional [57, 50, 55] tokens
  pure { userRequestID, username, userStatus, userStatusText }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have userStatusText := readOptional_part [57, 50, 55] record.userStatusText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [UserResponse.decode, userRequestID, username, userStatus, userStatusText, some_bind] <;> rfl

structure NoUsernames where
  username : Terminated 1  -- tag 553

def NoUsernames.parts (record : NoUsernames) : List Part :=
  [Part.required [53, 53, 51] record.username]

def NoUsernames.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]]]

theorem NoUsernames.shape (record : NoUsernames) : record.parts.map Part.tags = NoUsernames.tags := rfl

def NoUsernames.decode (tokens : List Token) : Option NoUsernames := do
  let username ← readRequired [53, 53, 51] tokens
  pure { username }

theorem NoUsernames.decode_agrees (record : NoUsernames) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUsernames.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUsernames.decode tokens = some record := by
  have distinct : NoUsernames.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoUsernames.decode, username, some_bind] <;> rfl

def NoUsernames.members : List (List UInt8) := NoUsernames.tags.flatten

def NoUsernames.encode (entry : NoUsernames) : List Token := encodeParts entry.parts

theorem NoUsernames.decode_encode (entry : NoUsernames) : NoUsernames.decode entry.encode = some entry :=
  NoUsernames.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUsernames.within (entry : NoUsernames) : ∀ token ∈ entry.encode, token.tag ∈ NoUsernames.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUsernames.shape] at this

theorem NoUsernames.led (entry : NoUsernames) : Lead [53, 53, 51] entry.encode :=
  lead_parts [53, 53, 51] entry.username _ NoUsernames.tags.tail rfl (by decide +kernel)

structure UserNotification where
  noUsernames : List NoUsernames  -- tag 809
  userStatus : Terminated 1  -- tag 926

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.group [56, 48, 57] NoUsernames.members NoUsernames.encode NoUsernames.within record.noUsernames,
   Part.required [57, 50, 54] record.userStatus]

def UserNotification.tags : List (List (List UInt8)) :=
  [[56, 48, 57] :: NoUsernames.members, [[57, 50, 54]]]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let noUsernames ← readGroup [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.decode tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  pure { noUsernames, userStatus }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have noUsernames := readGroup_part [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.encode NoUsernames.within NoUsernames.decode NoUsernames.decode_encode NoUsernames.led record.noUsernames tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [UserNotification.decode, noUsernames, userStatus, some_bind] <;> rfl

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  transactTime : Terminated 1  -- tag 60
  cxlRejResponseTo : Terminated 1  -- tag 434
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.required [54, 48] record.transactTime,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[54, 48]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, transactTime, cxlRejResponseTo, cxlRejReason, text }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, transactTime, cxlRejResponseTo, cxlRejReason, text, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier }

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

structure NoRegulatoryTradeIDs where
  regulatoryTradeID : Terminated 1  -- tag 1903
  regulatoryTradeIDType : Terminated 1  -- tag 1906

def NoRegulatoryTradeIDs.parts (record : NoRegulatoryTradeIDs) : List Part :=
  [Part.required [49, 57, 48, 51] record.regulatoryTradeID,
   Part.required [49, 57, 48, 54] record.regulatoryTradeIDType]

def NoRegulatoryTradeIDs.tags : List (List (List UInt8)) :=
  [[[49, 57, 48, 51]], [[49, 57, 48, 54]]]

theorem NoRegulatoryTradeIDs.shape (record : NoRegulatoryTradeIDs) : record.parts.map Part.tags = NoRegulatoryTradeIDs.tags := rfl

def NoRegulatoryTradeIDs.decode (tokens : List Token) : Option NoRegulatoryTradeIDs := do
  let regulatoryTradeID ← readRequired [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readRequired [49, 57, 48, 54] tokens
  pure { regulatoryTradeID, regulatoryTradeIDType }

theorem NoRegulatoryTradeIDs.decode_agrees (record : NoRegulatoryTradeIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRegulatoryTradeIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRegulatoryTradeIDs.decode tokens = some record := by
  have distinct : NoRegulatoryTradeIDs.tags.flatten.Nodup := by decide +kernel
  have regulatoryTradeID := readRequired_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have regulatoryTradeIDType := readRequired_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRegulatoryTradeIDs.decode, regulatoryTradeID, regulatoryTradeIDType, some_bind] <;> rfl

def NoRegulatoryTradeIDs.members : List (List UInt8) := NoRegulatoryTradeIDs.tags.flatten

def NoRegulatoryTradeIDs.encode (entry : NoRegulatoryTradeIDs) : List Token := encodeParts entry.parts

theorem NoRegulatoryTradeIDs.decode_encode (entry : NoRegulatoryTradeIDs) : NoRegulatoryTradeIDs.decode entry.encode = some entry :=
  NoRegulatoryTradeIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRegulatoryTradeIDs.within (entry : NoRegulatoryTradeIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRegulatoryTradeIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRegulatoryTradeIDs.shape] at this

theorem NoRegulatoryTradeIDs.led (entry : NoRegulatoryTradeIDs) : Lead [49, 57, 48, 51] entry.encode :=
  lead_parts [49, 57, 48, 51] entry.regulatoryTradeID _ NoRegulatoryTradeIDs.tags.tail rfl (by decide +kernel)

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

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  noPartyIDs : List NoPartyIDs  -- tag 453
  trdMatchID : Option (Terminated 1)  -- tag 880
  execID : Terminated 1  -- tag 17
  noRegulatoryTradeIDs : List NoRegulatoryTradeIDs  -- tag 1907
  execType : Terminated 1  -- tag 150
  ordStatus : Terminated 1  -- tag 39
  ordRejReason : Option (Terminated 1)  -- tag 103
  account : Option (Terminated 1)  -- tag 1
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
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
  timeInForce : Option (Terminated 1)  -- tag 59
  tradingSessionID : Option (Terminated 1)  -- tag 336
  expireDate : Option (Terminated 1)  -- tag 432
  execInst : Option (Terminated 1)  -- tag 18
  orderCapacity : Option (Terminated 1)  -- tag 528
  orderRestrictions : Option (Terminated 1)  -- tag 529
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  orderOrigination : Option (Terminated 1)  -- tag 1724
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  transactTime : Terminated 1  -- tag 60
  multiLegReportingType : Option (Terminated 1)  -- tag 442
  noLegs : List NoLegs  -- tag 555
  execRestatementReason : Option (Terminated 1)  -- tag 378
  allocID : Option (Terminated 1)  -- tag 70
  copyMsgIndicator : Option (Terminated 1)  -- tag 797
  matchIncrement : Option (Terminated 1)  -- tag 1089
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  text : Option (Terminated 1)  -- tag 58
  orderReference : Option (Terminated 1)  -- tag 20009
  selfMatchPreventionID : Option (Terminated 1)  -- tag 20015

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.required [49, 55] record.execID,
   Part.group [49, 57, 48, 55] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within record.noRegulatoryTradeIDs,
   Part.required [49, 53, 48] record.execType,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49] record.account,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
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
   Part.optional [53, 57] record.timeInForce,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [53, 50, 57] record.orderRestrictions,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.required [54, 48] record.transactTime,
   Part.optional [52, 52, 50] record.multiLegReportingType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [55, 48] record.allocID,
   Part.optional [55, 57, 55] record.copyMsgIndicator,
   Part.optional [49, 48, 56, 57] record.matchIncrement,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 48, 48, 57] record.orderReference,
   Part.optional [50, 48, 48, 49, 53] record.selfMatchPreventionID]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [52, 53, 51] :: NoPartyIDs.members, [[56, 56, 48]], [[49, 55]], [49, 57, 48, 55] :: NoRegulatoryTradeIDs.members, [[49, 53, 48]], [[51, 57]], [[49, 48, 51]], [[49]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 49, 48, 48]], [[49, 49, 48, 49]], [[49, 49, 48, 50]], [[49, 49, 49, 51]], [[49, 49, 48, 51]], [[49, 49, 48, 52]], [[49, 49, 48, 53]], [[49, 49, 48, 55]], [[49, 49, 48, 57]], [[53, 57]], [[51, 51, 54]], [[52, 51, 50]], [[49, 56]], [[53, 50, 56]], [[53, 50, 57]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[49, 55, 50, 52]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[49, 52]], [[54]], [[54, 48]], [[52, 52, 50]], [53, 53, 53] :: NoLegs.members, [[51, 55, 56]], [[55, 48]], [[55, 57, 55]], [[49, 48, 56, 57]], [[49, 49, 48]], [[49, 49, 49]], [[53, 56]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 53]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let execID ← readRequired [49, 55] tokens
  let noRegulatoryTradeIDs ← readGroup [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.decode tokens
  let execType ← readRequired [49, 53, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let account ← readOptional [49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
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
  let timeInForce ← readOptional [53, 57] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let orderRestrictions ← readOptional [53, 50, 57] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let transactTime ← readRequired [54, 48] tokens
  let multiLegReportingType ← readOptional [52, 52, 50] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let allocID ← readOptional [55, 48] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  let matchIncrement ← readOptional [49, 48, 56, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let text ← readOptional [53, 56] tokens
  let orderReference ← readOptional [50, 48, 48, 48, 57] tokens
  let selfMatchPreventionID ← readOptional [50, 48, 48, 49, 53] tokens
  pure { orderID, clOrdID, origClOrdID, noPartyIDs, trdMatchID, execID, noRegulatoryTradeIDs, execType, ordStatus, ordRejReason, account, symbol, securityID, securityIDSource, side, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerTradingSessionID, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, tradingSessionID, expireDate, execInst, orderCapacity, orderRestrictions, noOrderAttributes, orderOrigination, lastQty, lastPx, leavesQty, cumQty, avgPx, transactTime, multiLegReportingType, noLegs, execRestatementReason, allocID, copyMsgIndicator, matchIncrement, minQty, maxFloor, text, orderReference, selfMatchPreventionID }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noRegulatoryTradeIDs := readGroup_part [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within NoRegulatoryTradeIDs.decode NoRegulatoryTradeIDs.decode_encode NoRegulatoryTradeIDs.led record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have triggerType := readOptional_part [49, 49, 48, 48] record.triggerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have triggerAction := readOptional_part [49, 49, 48, 49] record.triggerAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have triggerPrice := readOptional_part [49, 49, 48, 50] record.triggerPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have triggerTradingSessionID := readOptional_part [49, 49, 49, 51] record.triggerTradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have triggerSymbol := readOptional_part [49, 49, 48, 51] record.triggerSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have triggerSecurityID := readOptional_part [49, 49, 48, 52] record.triggerSecurityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have triggerSecurityIDSource := readOptional_part [49, 49, 48, 53] record.triggerSecurityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have triggerPriceType := readOptional_part [49, 49, 48, 55] record.triggerPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have triggerPriceDirection := readOptional_part [49, 49, 48, 57] record.triggerPriceDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have orderRestrictions := readOptional_part [53, 50, 57] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have multiLegReportingType := readOptional_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have matchIncrement := readOptional_part [49, 48, 56, 57] record.matchIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have orderReference := readOptional_part [50, 48, 48, 48, 57] record.orderReference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [50, 48, 48, 49, 53] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, clOrdID, origClOrdID, noPartyIDs, trdMatchID, execID, noRegulatoryTradeIDs, execType, ordStatus, ordRejReason, account, symbol, securityID, securityIDSource, side, orderQty, ordType, price, triggerType, triggerAction, triggerPrice, triggerTradingSessionID, triggerSymbol, triggerSecurityID, triggerSecurityIDSource, triggerPriceType, triggerPriceDirection, timeInForce, tradingSessionID, expireDate, execInst, orderCapacity, orderRestrictions, noOrderAttributes, orderOrigination, lastQty, lastPx, leavesQty, cumQty, avgPx, transactTime, multiLegReportingType, noLegs, execRestatementReason, allocID, copyMsgIndicator, matchIncrement, minQty, maxFloor, text, orderReference, selfMatchPreventionID, some_bind] <;> rfl

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  businessRejectReason : Terminated 1  -- tag 380
  text : Option (Terminated 1)  -- tag 58

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [53, 56] record.text]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 56, 48]], [[53, 56]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, businessRejectReason, text }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, businessRejectReason, text, some_bind] <;> rfl

structure SecurityDefinition where
  securityReqID : Terminated 1  -- tag 320
  securityResponseType : Terminated 1  -- tag 323
  text : Option (Terminated 1)  -- tag 58
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 51] record.securityResponseType,
   Part.optional [53, 56] record.text,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 51]], [[53, 56]], [[53, 53]], [[52, 56]], [[50, 50]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseType ← readRequired [51, 50, 51] tokens
  let text ← readOptional [53, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { securityReqID, securityResponseType, text, symbol, securityID, securityIDSource }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseType := readRequired_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseType, text, symbol, securityID, securityIDSource, some_bind] <;> rfl

structure NoSecurityAltID where
  securityAltID : Terminated 1  -- tag 455
  securityAltIDSource : Terminated 1  -- tag 456

def NoSecurityAltID.parts (record : NoSecurityAltID) : List Part :=
  [Part.required [52, 53, 53] record.securityAltID,
   Part.required [52, 53, 54] record.securityAltIDSource]

def NoSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 53]], [[52, 53, 54]]]

theorem NoSecurityAltID.shape (record : NoSecurityAltID) : record.parts.map Part.tags = NoSecurityAltID.tags := rfl

def NoSecurityAltID.decode (tokens : List Token) : Option NoSecurityAltID := do
  let securityAltID ← readRequired [52, 53, 53] tokens
  let securityAltIDSource ← readRequired [52, 53, 54] tokens
  pure { securityAltID, securityAltIDSource }

theorem NoSecurityAltID.decode_agrees (record : NoSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSecurityAltID.decode tokens = some record := by
  have distinct : NoSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have securityAltID := readRequired_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityAltIDSource := readRequired_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoSecurityAltID.decode, securityAltID, securityAltIDSource, some_bind] <;> rfl

def NoSecurityAltID.members : List (List UInt8) := NoSecurityAltID.tags.flatten

def NoSecurityAltID.encode (entry : NoSecurityAltID) : List Token := encodeParts entry.parts

theorem NoSecurityAltID.decode_encode (entry : NoSecurityAltID) : NoSecurityAltID.decode entry.encode = some entry :=
  NoSecurityAltID.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSecurityAltID.within (entry : NoSecurityAltID) : ∀ token ∈ entry.encode, token.tag ∈ NoSecurityAltID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSecurityAltID.shape] at this

theorem NoSecurityAltID.led (entry : NoSecurityAltID) : Lead [52, 53, 53] entry.encode :=
  lead_parts [52, 53, 53] entry.securityAltID _ NoSecurityAltID.tags.tail rfl (by decide +kernel)

structure SecurityDefinitionUpdateReport where
  securityReqID : Terminated 1  -- tag 320
  securityUpdateAction : Terminated 1  -- tag 980
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionUpdateReport.parts (record : SecurityDefinitionUpdateReport) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [57, 56, 48] record.securityUpdateAction,
   Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionUpdateReport.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[57, 56, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionUpdateReport.shape (record : SecurityDefinitionUpdateReport) : record.parts.map Part.tags = SecurityDefinitionUpdateReport.tags := rfl

def SecurityDefinitionUpdateReport.decode (tokens : List Token) : Option SecurityDefinitionUpdateReport := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityUpdateAction ← readRequired [57, 56, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityUpdateAction, symbol, securityID, securityIDSource, noSecurityAltID, noLegs }

theorem SecurityDefinitionUpdateReport.decode_agrees (record : SecurityDefinitionUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionUpdateReport.decode tokens = some record := by
  have distinct : SecurityDefinitionUpdateReport.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityUpdateAction := readRequired_part [57, 56, 48] record.securityUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [SecurityDefinitionUpdateReport.decode, securityReqID, securityUpdateAction, symbol, securityID, securityIDSource, noSecurityAltID, noLegs, some_bind] <;> rfl

structure ListStatus where
  listID : Terminated 1  -- tag 66
  listStatusType : Terminated 1  -- tag 429
  noRpts : Terminated 1  -- tag 82
  listOrderStatus : Terminated 1  -- tag 431
  contingencyType : Terminated 1  -- tag 1385
  listRejectReason : Option (Terminated 1)  -- tag 1386
  rptSeq : Terminated 1  -- tag 83
  listStatusText : Option (Terminated 1)  -- tag 444
  transactTime : Option (Terminated 1)  -- tag 60
  totNoOrders : Terminated 1  -- tag 68

def ListStatus.parts (record : ListStatus) : List Part :=
  [Part.required [54, 54] record.listID,
   Part.required [52, 50, 57] record.listStatusType,
   Part.required [56, 50] record.noRpts,
   Part.required [52, 51, 49] record.listOrderStatus,
   Part.required [49, 51, 56, 53] record.contingencyType,
   Part.optional [49, 51, 56, 54] record.listRejectReason,
   Part.required [56, 51] record.rptSeq,
   Part.optional [52, 52, 52] record.listStatusText,
   Part.optional [54, 48] record.transactTime,
   Part.required [54, 56] record.totNoOrders]

def ListStatus.tags : List (List (List UInt8)) :=
  [[[54, 54]], [[52, 50, 57]], [[56, 50]], [[52, 51, 49]], [[49, 51, 56, 53]], [[49, 51, 56, 54]], [[56, 51]], [[52, 52, 52]], [[54, 48]], [[54, 56]]]

theorem ListStatus.shape (record : ListStatus) : record.parts.map Part.tags = ListStatus.tags := rfl

def ListStatus.decode (tokens : List Token) : Option ListStatus := do
  let listID ← readRequired [54, 54] tokens
  let listStatusType ← readRequired [52, 50, 57] tokens
  let noRpts ← readRequired [56, 50] tokens
  let listOrderStatus ← readRequired [52, 51, 49] tokens
  let contingencyType ← readRequired [49, 51, 56, 53] tokens
  let listRejectReason ← readOptional [49, 51, 56, 54] tokens
  let rptSeq ← readRequired [56, 51] tokens
  let listStatusText ← readOptional [52, 52, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let totNoOrders ← readRequired [54, 56] tokens
  pure { listID, listStatusType, noRpts, listOrderStatus, contingencyType, listRejectReason, rptSeq, listStatusText, transactTime, totNoOrders }

theorem ListStatus.decode_agrees (record : ListStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ ListStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ListStatus.decode tokens = some record := by
  have distinct : ListStatus.tags.flatten.Nodup := by decide +kernel
  have listID := readRequired_part [54, 54] record.listID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have listStatusType := readRequired_part [52, 50, 57] record.listStatusType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRpts := readRequired_part [56, 50] record.noRpts tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have listOrderStatus := readRequired_part [52, 51, 49] record.listOrderStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have contingencyType := readRequired_part [49, 51, 56, 53] record.contingencyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have listRejectReason := readOptional_part [49, 51, 56, 54] record.listRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have rptSeq := readRequired_part [56, 51] record.rptSeq tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have listStatusText := readOptional_part [52, 52, 52] record.listStatusText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have totNoOrders := readRequired_part [54, 56] record.totNoOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [ListStatus.decode, listID, listStatusType, noRpts, listOrderStatus, contingencyType, listRejectReason, rptSeq, listStatusText, transactTime, totNoOrders, some_bind] <;> rfl

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

structure MassQuoteAcknowledgement where
  quoteID : Option (Terminated 1)  -- tag 117
  quoteStatus : Terminated 1  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  quoteResponseLevel : Terminated 1  -- tag 301
  orderID : Option (Terminated 1)  -- tag 37
  quoteType : Terminated 1  -- tag 537
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  noQuoteSets : List NoQuoteSets  -- tag 296
  text : Option (Terminated 1)  -- tag 58

def MassQuoteAcknowledgement.parts (record : MassQuoteAcknowledgement) : List Part :=
  [Part.optional [49, 49, 55] record.quoteID,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.required [51, 48, 49] record.quoteResponseLevel,
   Part.optional [51, 55] record.orderID,
   Part.required [53, 51, 55] record.quoteType,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.group [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within record.noQuoteSets,
   Part.optional [53, 56] record.text]

def MassQuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[50, 57, 55]], [[51, 48, 48]], [[51, 48, 49]], [[51, 55]], [[53, 51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [50, 57, 54] :: NoQuoteSets.members, [[53, 56]]]

theorem MassQuoteAcknowledgement.shape (record : MassQuoteAcknowledgement) : record.parts.map Part.tags = MassQuoteAcknowledgement.tags := rfl

def MassQuoteAcknowledgement.decode (tokens : List Token) : Option MassQuoteAcknowledgement := do
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let quoteResponseLevel ← readRequired [51, 48, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let quoteType ← readRequired [53, 51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let noQuoteSets ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteID, quoteStatus, quoteRejectReason, quoteResponseLevel, orderID, quoteType, noPartyIDs, account, noQuoteSets, text }

theorem MassQuoteAcknowledgement.decode_agrees (record : MassQuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuoteAcknowledgement.decode tokens = some record := by
  have distinct : MassQuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteResponseLevel := readRequired_part [51, 48, 49] record.quoteResponseLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quoteType := readRequired_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noQuoteSets := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within NoQuoteSets.decode NoQuoteSets.decode_encode NoQuoteSets.led record.noQuoteSets tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [MassQuoteAcknowledgement.decode, quoteID, quoteStatus, quoteRejectReason, quoteResponseLevel, orderID, quoteType, noPartyIDs, account, noQuoteSets, text, some_bind] <;> rfl

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  minQty : Option (Terminated 1)  -- tag 110
  exposureDuration : Option (Terminated 1)  -- tag 1629
  transactTime : Option (Terminated 1)  -- tag 60
  account : Option (Terminated 1)  -- tag 1
  quoteRequestType : Option (Terminated 1)  -- tag 303
  orderQty : Option (Terminated 1)  -- tag 38
  price : Option (Terminated 1)  -- tag 44
  rfqExecutionDelay : Option (Terminated 1)  -- tag 20016
  noPartyIDs : List NoPartyIDs  -- tag 453

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [53, 52] record.side,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 54, 50, 57] record.exposureDuration,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49] record.account,
   Part.optional [51, 48, 51] record.quoteRequestType,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 52] record.price,
   Part.optional [50, 48, 48, 49, 54] record.rfqExecutionDelay,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[49, 49, 48]], [[49, 54, 50, 57]], [[54, 48]], [[49]], [[51, 48, 51]], [[51, 56]], [[52, 52]], [[50, 48, 48, 49, 54]], [52, 53, 51] :: NoPartyIDs.members]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let exposureDuration ← readOptional [49, 54, 50, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let account ← readOptional [49] tokens
  let quoteRequestType ← readOptional [51, 48, 51] tokens
  let orderQty ← readOptional [51, 56] tokens
  let price ← readOptional [52, 52] tokens
  let rfqExecutionDelay ← readOptional [50, 48, 48, 49, 54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { symbol, securityID, securityIDSource, side, minQty, exposureDuration, transactTime, account, quoteRequestType, orderQty, price, rfqExecutionDelay, noPartyIDs }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have exposureDuration := readOptional_part [49, 54, 50, 57] record.exposureDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have quoteRequestType := readOptional_part [51, 48, 51] record.quoteRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have rfqExecutionDelay := readOptional_part [50, 48, 48, 49, 54] record.rfqExecutionDelay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, side, minQty, exposureDuration, transactTime, account, quoteRequestType, orderQty, price, rfqExecutionDelay, noPartyIDs, some_bind] <;> rfl

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

structure QuoteRequestReject where
  quoteReqID : Terminated 1  -- tag 131
  quoteRequestRejectReason : Terminated 1  -- tag 658
  noRelatedSym : List NoRelatedSym  -- tag 146
  text : Option (Terminated 1)  -- tag 58

def QuoteRequestReject.parts (record : QuoteRequestReject) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.required [54, 53, 56] record.quoteRequestRejectReason,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.optional [53, 56] record.text]

def QuoteRequestReject.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[54, 53, 56]], [49, 52, 54] :: NoRelatedSym.members, [[53, 56]]]

theorem QuoteRequestReject.shape (record : QuoteRequestReject) : record.parts.map Part.tags = QuoteRequestReject.tags := rfl

def QuoteRequestReject.decode (tokens : List Token) : Option QuoteRequestReject := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let quoteRequestRejectReason ← readRequired [54, 53, 56] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteReqID, quoteRequestRejectReason, noRelatedSym, text }

theorem QuoteRequestReject.decode_agrees (record : QuoteRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequestReject.decode tokens = some record := by
  have distinct : QuoteRequestReject.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteRequestRejectReason := readRequired_part [54, 53, 56] record.quoteRequestRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [QuoteRequestReject.decode, quoteReqID, quoteRequestRejectReason, noRelatedSym, text, some_bind] <;> rfl

structure QuoteRequest where
  quoteReqID : Option (Terminated 1)  -- tag 131
  privateQuote : Option (Terminated 1)  -- tag 1171
  noRelatedSym : List NoRelatedSym  -- tag 146

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [49, 49, 55, 49] record.privateQuote,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[49, 49, 55, 49]], [49, 52, 54] :: NoRelatedSym.members]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let privateQuote ← readOptional [49, 49, 55, 49] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { quoteReqID, privateQuote, noRelatedSym }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have privateQuote := readOptional_part [49, 49, 55, 49] record.privateQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [QuoteRequest.decode, quoteReqID, privateQuote, noRelatedSym, some_bind] <;> rfl

structure Quote where
  quoteReqID : Terminated 1  -- tag 131
  quoteID : Terminated 1  -- tag 117
  quoteType : Terminated 1  -- tag 537
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  side : Terminated 1  -- tag 54
  bidPx : Option (Terminated 1)  -- tag 132
  offerPx : Option (Terminated 1)  -- tag 133
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135
  exposureDuration : Option (Terminated 1)  -- tag 1629

def Quote.parts (record : Quote) : List Part :=
  [Part.required [49, 51, 49] record.quoteReqID,
   Part.required [49, 49, 55] record.quoteID,
   Part.required [53, 51, 55] record.quoteType,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 52] record.side,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [49, 54, 50, 57] record.exposureDuration]

def Quote.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[49, 49, 55]], [[53, 51, 55]], [[53, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]], [[49, 54, 50, 57]]]

theorem Quote.shape (record : Quote) : record.parts.map Part.tags = Quote.tags := rfl

def Quote.decode (tokens : List Token) : Option Quote := do
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteType ← readRequired [53, 51, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let side ← readRequired [53, 52] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let exposureDuration ← readOptional [49, 54, 50, 57] tokens
  pure { quoteReqID, quoteID, quoteType, symbol, securityID, securityIDSource, side, bidPx, offerPx, bidSize, offerSize, exposureDuration }

theorem Quote.decode_agrees (record : Quote) (tokens : List Token)
    (agrees : ∀ tags ∈ Quote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Quote.decode tokens = some record := by
  have distinct : Quote.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteType := readRequired_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have exposureDuration := readOptional_part [49, 54, 50, 57] record.exposureDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Quote.decode, quoteReqID, quoteID, quoteType, symbol, securityID, securityIDSource, side, bidPx, offerPx, bidSize, offerSize, exposureDuration, some_bind] <;> rfl

structure QuoteStatusReport where
  quoteReqID : Option (Terminated 1)  -- tag 131
  quoteMsgID : Option (Terminated 1)  -- tag 1166
  quoteType : Option (Terminated 1)  -- tag 537
  quoteStatus : Option (Terminated 1)  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  text : Option (Terminated 1)  -- tag 58

def QuoteStatusReport.parts (record : QuoteStatusReport) : List Part :=
  [Part.optional [49, 51, 49] record.quoteReqID,
   Part.optional [49, 49, 54, 54] record.quoteMsgID,
   Part.optional [53, 51, 55] record.quoteType,
   Part.optional [50, 57, 55] record.quoteStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.optional [53, 56] record.text]

def QuoteStatusReport.tags : List (List (List UInt8)) :=
  [[[49, 51, 49]], [[49, 49, 54, 54]], [[53, 51, 55]], [[50, 57, 55]], [[51, 48, 48]], [[53, 56]]]

theorem QuoteStatusReport.shape (record : QuoteStatusReport) : record.parts.map Part.tags = QuoteStatusReport.tags := rfl

def QuoteStatusReport.decode (tokens : List Token) : Option QuoteStatusReport := do
  let quoteReqID ← readOptional [49, 51, 49] tokens
  let quoteMsgID ← readOptional [49, 49, 54, 54] tokens
  let quoteType ← readOptional [53, 51, 55] tokens
  let quoteStatus ← readOptional [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteReqID, quoteMsgID, quoteType, quoteStatus, quoteRejectReason, text }

theorem QuoteStatusReport.decode_agrees (record : QuoteStatusReport) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteStatusReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteStatusReport.decode tokens = some record := by
  have distinct : QuoteStatusReport.tags.flatten.Nodup := by decide +kernel
  have quoteReqID := readOptional_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteMsgID := readOptional_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteType := readOptional_part [53, 51, 55] record.quoteType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteStatus := readOptional_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [QuoteStatusReport.decode, quoteReqID, quoteMsgID, quoteType, quoteStatus, quoteRejectReason, text, some_bind] <;> rfl

structure OneSidedAuctionRequestAck where
  auctionRequestID : Terminated 1  -- tag 20001
  origAuctionRequestID : Option (Terminated 1)  -- tag 20012
  auctionRequestResult : Option (Terminated 1)  -- tag 20005
  text : Option (Terminated 1)  -- tag 58

def OneSidedAuctionRequestAck.parts (record : OneSidedAuctionRequestAck) : List Part :=
  [Part.required [50, 48, 48, 48, 49] record.auctionRequestID,
   Part.optional [50, 48, 48, 49, 50] record.origAuctionRequestID,
   Part.optional [50, 48, 48, 48, 53] record.auctionRequestResult,
   Part.optional [53, 56] record.text]

def OneSidedAuctionRequestAck.tags : List (List (List UInt8)) :=
  [[[50, 48, 48, 48, 49]], [[50, 48, 48, 49, 50]], [[50, 48, 48, 48, 53]], [[53, 56]]]

theorem OneSidedAuctionRequestAck.shape (record : OneSidedAuctionRequestAck) : record.parts.map Part.tags = OneSidedAuctionRequestAck.tags := rfl

def OneSidedAuctionRequestAck.decode (tokens : List Token) : Option OneSidedAuctionRequestAck := do
  let auctionRequestID ← readRequired [50, 48, 48, 48, 49] tokens
  let origAuctionRequestID ← readOptional [50, 48, 48, 49, 50] tokens
  let auctionRequestResult ← readOptional [50, 48, 48, 48, 53] tokens
  let text ← readOptional [53, 56] tokens
  pure { auctionRequestID, origAuctionRequestID, auctionRequestResult, text }

theorem OneSidedAuctionRequestAck.decode_agrees (record : OneSidedAuctionRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ OneSidedAuctionRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OneSidedAuctionRequestAck.decode tokens = some record := by
  have distinct : OneSidedAuctionRequestAck.tags.flatten.Nodup := by decide +kernel
  have auctionRequestID := readRequired_part [50, 48, 48, 48, 49] record.auctionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origAuctionRequestID := readOptional_part [50, 48, 48, 49, 50] record.origAuctionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have auctionRequestResult := readOptional_part [50, 48, 48, 48, 53] record.auctionRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [OneSidedAuctionRequestAck.decode, auctionRequestID, origAuctionRequestID, auctionRequestResult, text, some_bind] <;> rfl

structure TradeCaptureReportAck where
  tradeReportID : Terminated 1  -- tag 571
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  dealID : Option (Terminated 1)  -- tag 21000
  tradeReportType : Option (Terminated 1)  -- tag 856
  secondaryTradeReportID : Option (Terminated 1)  -- tag 818
  execType : Terminated 1  -- tag 150
  trdRptStatus : Option (Terminated 1)  -- tag 939
  tradeReportRejectReason : Option (Terminated 1)  -- tag 751
  tradeHandlingInstr : Option (Terminated 1)  -- tag 1123
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  tradeID : Option (Terminated 1)  -- tag 1003
  allocID : Option (Terminated 1)  -- tag 70
  account : Option (Terminated 1)  -- tag 1
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [50, 49, 48, 48, 48] record.dealID,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [56, 49, 56] record.secondaryTradeReportID,
   Part.required [49, 53, 48] record.execType,
   Part.optional [57, 51, 57] record.trdRptStatus,
   Part.optional [55, 53, 49] record.tradeReportRejectReason,
   Part.optional [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [55, 48] record.allocID,
   Part.optional [49] record.account,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[52, 56, 55]], [[50, 49, 48, 48, 48]], [[56, 53, 54]], [[56, 49, 56]], [[49, 53, 48]], [[57, 51, 57]], [[55, 53, 49]], [[49, 49, 50, 51]], [[53, 53]], [[53, 56]], [[52, 56]], [[50, 50]], [[49, 48, 48, 51]], [[55, 48]], [[49]], [[55, 57, 55]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let dealID ← readOptional [50, 49, 48, 48, 48] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let secondaryTradeReportID ← readOptional [56, 49, 56] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let trdRptStatus ← readOptional [57, 51, 57] tokens
  let tradeReportRejectReason ← readOptional [55, 53, 49] tokens
  let tradeHandlingInstr ← readOptional [49, 49, 50, 51] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let allocID ← readOptional [55, 48] tokens
  let account ← readOptional [49] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { tradeReportID, tradeReportTransType, dealID, tradeReportType, secondaryTradeReportID, execType, trdRptStatus, tradeReportRejectReason, tradeHandlingInstr, symbol, text, securityID, securityIDSource, tradeID, allocID, account, copyMsgIndicator }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have dealID := readOptional_part [50, 49, 48, 48, 48] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have secondaryTradeReportID := readOptional_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have trdRptStatus := readOptional_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeReportRejectReason := readOptional_part [55, 53, 49] record.tradeReportRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeHandlingInstr := readOptional_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, tradeReportID, tradeReportTransType, dealID, tradeReportType, secondaryTradeReportID, execType, trdRptStatus, tradeReportRejectReason, tradeHandlingInstr, symbol, text, securityID, securityIDSource, tradeID, allocID, account, copyMsgIndicator, some_bind] <;> rfl

structure NoRootPartyIDs where
  rootPartyID : Terminated 1  -- tag 1117
  rootPartyIDSource : Option (Terminated 1)  -- tag 1118
  rootPartyRole : Option (Terminated 1)  -- tag 1119
  rootPartyRoleQualifier : Option (Terminated 1)  -- tag 2388

def NoRootPartyIDs.parts (record : NoRootPartyIDs) : List Part :=
  [Part.required [49, 49, 49, 55] record.rootPartyID,
   Part.optional [49, 49, 49, 56] record.rootPartyIDSource,
   Part.optional [49, 49, 49, 57] record.rootPartyRole,
   Part.optional [50, 51, 56, 56] record.rootPartyRoleQualifier]

def NoRootPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 49, 49, 55]], [[49, 49, 49, 56]], [[49, 49, 49, 57]], [[50, 51, 56, 56]]]

theorem NoRootPartyIDs.shape (record : NoRootPartyIDs) : record.parts.map Part.tags = NoRootPartyIDs.tags := rfl

def NoRootPartyIDs.decode (tokens : List Token) : Option NoRootPartyIDs := do
  let rootPartyID ← readRequired [49, 49, 49, 55] tokens
  let rootPartyIDSource ← readOptional [49, 49, 49, 56] tokens
  let rootPartyRole ← readOptional [49, 49, 49, 57] tokens
  let rootPartyRoleQualifier ← readOptional [50, 51, 56, 56] tokens
  pure { rootPartyID, rootPartyIDSource, rootPartyRole, rootPartyRoleQualifier }

theorem NoRootPartyIDs.decode_agrees (record : NoRootPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRootPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRootPartyIDs.decode tokens = some record := by
  have distinct : NoRootPartyIDs.tags.flatten.Nodup := by decide +kernel
  have rootPartyID := readRequired_part [49, 49, 49, 55] record.rootPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rootPartyIDSource := readOptional_part [49, 49, 49, 56] record.rootPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rootPartyRole := readOptional_part [49, 49, 49, 57] record.rootPartyRole tokens
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

structure NoTrdRegPublications where
  trdRegPublicationType : Terminated 1  -- tag 2669
  trdRegPublicationReason : Option (Terminated 1)  -- tag 2670

def NoTrdRegPublications.parts (record : NoTrdRegPublications) : List Part :=
  [Part.required [50, 54, 54, 57] record.trdRegPublicationType,
   Part.optional [50, 54, 55, 48] record.trdRegPublicationReason]

def NoTrdRegPublications.tags : List (List (List UInt8)) :=
  [[[50, 54, 54, 57]], [[50, 54, 55, 48]]]

theorem NoTrdRegPublications.shape (record : NoTrdRegPublications) : record.parts.map Part.tags = NoTrdRegPublications.tags := rfl

def NoTrdRegPublications.decode (tokens : List Token) : Option NoTrdRegPublications := do
  let trdRegPublicationType ← readRequired [50, 54, 54, 57] tokens
  let trdRegPublicationReason ← readOptional [50, 54, 55, 48] tokens
  pure { trdRegPublicationType, trdRegPublicationReason }

theorem NoTrdRegPublications.decode_agrees (record : NoTrdRegPublications) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTrdRegPublications.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTrdRegPublications.decode tokens = some record := by
  have distinct : NoTrdRegPublications.tags.flatten.Nodup := by decide +kernel
  have trdRegPublicationType := readRequired_part [50, 54, 54, 57] record.trdRegPublicationType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have trdRegPublicationReason := readOptional_part [50, 54, 55, 48] record.trdRegPublicationReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTrdRegPublications.decode, trdRegPublicationType, trdRegPublicationReason, some_bind] <;> rfl

def NoTrdRegPublications.members : List (List UInt8) := NoTrdRegPublications.tags.flatten

def NoTrdRegPublications.encode (entry : NoTrdRegPublications) : List Token := encodeParts entry.parts

theorem NoTrdRegPublications.decode_encode (entry : NoTrdRegPublications) : NoTrdRegPublications.decode entry.encode = some entry :=
  NoTrdRegPublications.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTrdRegPublications.within (entry : NoTrdRegPublications) : ∀ token ∈ entry.encode, token.tag ∈ NoTrdRegPublications.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTrdRegPublications.shape] at this

theorem NoTrdRegPublications.led (entry : NoTrdRegPublications) : Lead [50, 54, 54, 57] entry.encode :=
  lead_parts [50, 54, 54, 57] entry.trdRegPublicationType _ NoTrdRegPublications.tags.tail rfl (by decide +kernel)

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  tradeID : Option (Terminated 1)  -- tag 1003
  secondaryTradeID : Option (Terminated 1)  -- tag 1040
  origTradeID : Option (Terminated 1)  -- tag 1126
  origSecondaryTradeID : Option (Terminated 1)  -- tag 1127
  tradeReportRefID : Option (Terminated 1)  -- tag 572
  secondaryTradeReportID : Option (Terminated 1)  -- tag 818
  tradeReportTransType : Terminated 1  -- tag 487
  tradeReportType : Terminated 1  -- tag 856
  tradeHandlingInstr : Option (Terminated 1)  -- tag 1123
  offBookType : Option (Terminated 1)  -- tag 20202
  cCPTrdType : Option (Terminated 1)  -- tag 21023
  orderCategory : Option (Terminated 1)  -- tag 1115
  trdType : Option (Terminated 1)  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  matchStatus : Terminated 1  -- tag 573
  trdMatchID : Option (Terminated 1)  -- tag 880
  noRegulatoryTradeIDs : List NoRegulatoryTradeIDs  -- tag 1907
  previouslyReported : Option (Terminated 1)  -- tag 570
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  symbol : Terminated 1  -- tag 55
  noLegs : List NoLegs  -- tag 555
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  orderQty : Option (Terminated 1)  -- tag 38
  lastQty : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  settlDate : Option (Terminated 1)  -- tag 64
  lastMkt : Option (Terminated 1)  -- tag 30
  venueType : Option (Terminated 1)  -- tag 1430
  matchType : Option (Terminated 1)  -- tag 574
  noSides : List NoSides  -- tag 552
  clearingBusinessDate : Option (Terminated 1)  -- tag 715
  secondaryAllocID : Option (Terminated 1)  -- tag 793
  dealID : Option (Terminated 1)  -- tag 21000
  gIDealSource : Option (Terminated 1)  -- tag 21024
  nasdaqTradeCondition : Option (Terminated 1)  -- tag 21025
  tradeReportState : Option (Terminated 1)  -- tag 21013
  tradeReportSubState : Option (Terminated 1)  -- tag 21014
  tradeReportInstrType : Option (Terminated 1)  -- tag 21015
  traderReportReason : Option (Terminated 1)  -- tag 21016
  authorizationState : Option (Terminated 1)  -- tag 21017
  affimationState : Option (Terminated 1)  -- tag 21018
  deliveryUnit : Option (Terminated 1)  -- tag 21019
  origClearingBusinessDate : Option (Terminated 1)  -- tag 21020
  strategyMarker : Option (Terminated 1)  -- tag 21021
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  noTrdRegPublications : List NoTrdRegPublications  -- tag 2668
  regulatoryReportType : Option (Terminated 1)  -- tag 1934
  correspondingPrice : Option (Terminated 1)  -- tag 20007
  consideration : Option (Terminated 1)  -- tag 20008
  deferredPublicationTime : Option (Terminated 1)  -- tag 20013
  copyMsgIndicator : Option (Terminated 1)  -- tag 797

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [49, 48, 52, 48] record.secondaryTradeID,
   Part.optional [49, 49, 50, 54] record.origTradeID,
   Part.optional [49, 49, 50, 55] record.origSecondaryTradeID,
   Part.optional [53, 55, 50] record.tradeReportRefID,
   Part.optional [56, 49, 56] record.secondaryTradeReportID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.optional [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [50, 48, 50, 48, 50] record.offBookType,
   Part.optional [50, 49, 48, 50, 51] record.cCPTrdType,
   Part.optional [49, 49, 49, 53] record.orderCategory,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.required [53, 55, 51] record.matchStatus,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.group [49, 57, 48, 55] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within record.noRegulatoryTradeIDs,
   Part.optional [53, 55, 48] record.previouslyReported,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [51, 56] record.orderQty,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 49] record.lastPx,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 52] record.settlDate,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.optional [53, 55, 52] record.matchType,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [55, 49, 53] record.clearingBusinessDate,
   Part.optional [55, 57, 51] record.secondaryAllocID,
   Part.optional [50, 49, 48, 48, 48] record.dealID,
   Part.optional [50, 49, 48, 50, 52] record.gIDealSource,
   Part.optional [50, 49, 48, 50, 53] record.nasdaqTradeCondition,
   Part.optional [50, 49, 48, 49, 51] record.tradeReportState,
   Part.optional [50, 49, 48, 49, 52] record.tradeReportSubState,
   Part.optional [50, 49, 48, 49, 53] record.tradeReportInstrType,
   Part.optional [50, 49, 48, 49, 54] record.traderReportReason,
   Part.optional [50, 49, 48, 49, 55] record.authorizationState,
   Part.optional [50, 49, 48, 49, 56] record.affimationState,
   Part.optional [50, 49, 48, 49, 57] record.deliveryUnit,
   Part.optional [50, 49, 48, 50, 48] record.origClearingBusinessDate,
   Part.optional [50, 49, 48, 50, 49] record.strategyMarker,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.group [50, 54, 54, 56] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within record.noTrdRegPublications,
   Part.optional [49, 57, 51, 52] record.regulatoryReportType,
   Part.optional [50, 48, 48, 48, 55] record.correspondingPrice,
   Part.optional [50, 48, 48, 48, 56] record.consideration,
   Part.optional [50, 48, 48, 49, 51] record.deferredPublicationTime,
   Part.optional [55, 57, 55] record.copyMsgIndicator]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[49, 48, 48, 51]], [[49, 48, 52, 48]], [[49, 49, 50, 54]], [[49, 49, 50, 55]], [[53, 55, 50]], [[56, 49, 56]], [[52, 56, 55]], [[56, 53, 54]], [[49, 49, 50, 51]], [[50, 48, 50, 48, 50]], [[50, 49, 48, 50, 51]], [[49, 49, 49, 53]], [[56, 50, 56]], [[56, 50, 57]], [[56, 53, 53]], [[53, 55, 51]], [[56, 56, 48]], [49, 57, 48, 55] :: NoRegulatoryTradeIDs.members, [[53, 55, 48]], [49, 49, 49, 54] :: NoRootPartyIDs.members, [[53, 53]], [53, 53, 53] :: NoLegs.members, [[52, 56]], [[50, 50]], [[51, 56]], [[51, 50]], [[51, 49]], [[55, 53]], [[54, 48]], [[54, 52]], [[51, 48]], [[49, 52, 51, 48]], [[53, 55, 52]], [53, 53, 50] :: NoSides.members, [[55, 49, 53]], [[55, 57, 51]], [[50, 49, 48, 48, 48]], [[50, 49, 48, 50, 52]], [[50, 49, 48, 50, 53]], [[50, 49, 48, 49, 51]], [[50, 49, 48, 49, 52]], [[50, 49, 48, 49, 53]], [[50, 49, 48, 49, 54]], [[50, 49, 48, 49, 55]], [[50, 49, 48, 49, 56]], [[50, 49, 48, 49, 57]], [[50, 49, 48, 50, 48]], [[50, 49, 48, 50, 49]], [[49, 51, 57, 48]], [50, 54, 54, 56] :: NoTrdRegPublications.members, [[49, 57, 51, 52]], [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 49, 51]], [[55, 57, 55]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let secondaryTradeID ← readOptional [49, 48, 52, 48] tokens
  let origTradeID ← readOptional [49, 49, 50, 54] tokens
  let origSecondaryTradeID ← readOptional [49, 49, 50, 55] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  let secondaryTradeReportID ← readOptional [56, 49, 56] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeHandlingInstr ← readOptional [49, 49, 50, 51] tokens
  let offBookType ← readOptional [50, 48, 50, 48, 50] tokens
  let cCPTrdType ← readOptional [50, 49, 48, 50, 51] tokens
  let orderCategory ← readOptional [49, 49, 49, 53] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let matchStatus ← readRequired [53, 55, 51] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let noRegulatoryTradeIDs ← readGroup [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.decode tokens
  let previouslyReported ← readOptional [53, 55, 48] tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let orderQty ← readOptional [51, 56] tokens
  let lastQty ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let settlDate ← readOptional [54, 52] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let clearingBusinessDate ← readOptional [55, 49, 53] tokens
  let secondaryAllocID ← readOptional [55, 57, 51] tokens
  let dealID ← readOptional [50, 49, 48, 48, 48] tokens
  let gIDealSource ← readOptional [50, 49, 48, 50, 52] tokens
  let nasdaqTradeCondition ← readOptional [50, 49, 48, 50, 53] tokens
  let tradeReportState ← readOptional [50, 49, 48, 49, 51] tokens
  let tradeReportSubState ← readOptional [50, 49, 48, 49, 52] tokens
  let tradeReportInstrType ← readOptional [50, 49, 48, 49, 53] tokens
  let traderReportReason ← readOptional [50, 49, 48, 49, 54] tokens
  let authorizationState ← readOptional [50, 49, 48, 49, 55] tokens
  let affimationState ← readOptional [50, 49, 48, 49, 56] tokens
  let deliveryUnit ← readOptional [50, 49, 48, 49, 57] tokens
  let origClearingBusinessDate ← readOptional [50, 49, 48, 50, 48] tokens
  let strategyMarker ← readOptional [50, 49, 48, 50, 49] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let noTrdRegPublications ← readGroup [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.decode tokens
  let regulatoryReportType ← readOptional [49, 57, 51, 52] tokens
  let correspondingPrice ← readOptional [50, 48, 48, 48, 55] tokens
  let consideration ← readOptional [50, 48, 48, 48, 56] tokens
  let deferredPublicationTime ← readOptional [50, 48, 48, 49, 51] tokens
  let copyMsgIndicator ← readOptional [55, 57, 55] tokens
  pure { tradeReportID, tradeID, secondaryTradeID, origTradeID, origSecondaryTradeID, tradeReportRefID, secondaryTradeReportID, tradeReportTransType, tradeReportType, tradeHandlingInstr, offBookType, cCPTrdType, orderCategory, trdType, trdSubType, secondaryTrdType, matchStatus, trdMatchID, noRegulatoryTradeIDs, previouslyReported, noRootPartyIDs, symbol, noLegs, securityID, securityIDSource, orderQty, lastQty, lastPx, tradeDate, transactTime, settlDate, lastMkt, venueType, matchType, noSides, clearingBusinessDate, secondaryAllocID, dealID, gIDealSource, nasdaqTradeCondition, tradeReportState, tradeReportSubState, tradeReportInstrType, traderReportReason, authorizationState, affimationState, deliveryUnit, origClearingBusinessDate, strategyMarker, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, correspondingPrice, consideration, deferredPublicationTime, copyMsgIndicator }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryTradeID := readOptional_part [49, 48, 52, 48] record.secondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origTradeID := readOptional_part [49, 49, 50, 54] record.origTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origSecondaryTradeID := readOptional_part [49, 49, 50, 55] record.origSecondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have secondaryTradeReportID := readOptional_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeHandlingInstr := readOptional_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have offBookType := readOptional_part [50, 48, 50, 48, 50] record.offBookType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have cCPTrdType := readOptional_part [50, 49, 48, 50, 51] record.cCPTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderCategory := readOptional_part [49, 49, 49, 53] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have matchStatus := readRequired_part [53, 55, 51] record.matchStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noRegulatoryTradeIDs := readGroup_part [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within NoRegulatoryTradeIDs.decode NoRegulatoryTradeIDs.decode_encode NoRegulatoryTradeIDs.led record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have previouslyReported := readOptional_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have clearingBusinessDate := readOptional_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have secondaryAllocID := readOptional_part [55, 57, 51] record.secondaryAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have dealID := readOptional_part [50, 49, 48, 48, 48] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have gIDealSource := readOptional_part [50, 49, 48, 50, 52] record.gIDealSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have nasdaqTradeCondition := readOptional_part [50, 49, 48, 50, 53] record.nasdaqTradeCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have tradeReportState := readOptional_part [50, 49, 48, 49, 51] record.tradeReportState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have tradeReportSubState := readOptional_part [50, 49, 48, 49, 52] record.tradeReportSubState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tradeReportInstrType := readOptional_part [50, 49, 48, 49, 53] record.tradeReportInstrType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have traderReportReason := readOptional_part [50, 49, 48, 49, 54] record.traderReportReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have authorizationState := readOptional_part [50, 49, 48, 49, 55] record.authorizationState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have affimationState := readOptional_part [50, 49, 48, 49, 56] record.affimationState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have deliveryUnit := readOptional_part [50, 49, 48, 49, 57] record.deliveryUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have origClearingBusinessDate := readOptional_part [50, 49, 48, 50, 48] record.origClearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have strategyMarker := readOptional_part [50, 49, 48, 50, 49] record.strategyMarker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have noTrdRegPublications := readGroup_part [50, 54, 54, 56] [50, 54, 54, 57] NoTrdRegPublications.members NoTrdRegPublications.encode NoTrdRegPublications.within NoTrdRegPublications.decode NoTrdRegPublications.decode_encode NoTrdRegPublications.led record.noTrdRegPublications tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have regulatoryReportType := readOptional_part [49, 57, 51, 52] record.regulatoryReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have correspondingPrice := readOptional_part [50, 48, 48, 48, 55] record.correspondingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have consideration := readOptional_part [50, 48, 48, 48, 56] record.consideration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have deferredPublicationTime := readOptional_part [50, 48, 48, 49, 51] record.deferredPublicationTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have copyMsgIndicator := readOptional_part [55, 57, 55] record.copyMsgIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, tradeID, secondaryTradeID, origTradeID, origSecondaryTradeID, tradeReportRefID, secondaryTradeReportID, tradeReportTransType, tradeReportType, tradeHandlingInstr, offBookType, cCPTrdType, orderCategory, trdType, trdSubType, secondaryTrdType, matchStatus, trdMatchID, noRegulatoryTradeIDs, previouslyReported, noRootPartyIDs, symbol, noLegs, securityID, securityIDSource, orderQty, lastQty, lastPx, tradeDate, transactTime, settlDate, lastMkt, venueType, matchType, noSides, clearingBusinessDate, secondaryAllocID, dealID, gIDealSource, nasdaqTradeCondition, tradeReportState, tradeReportSubState, tradeReportInstrType, traderReportReason, authorizationState, affimationState, deliveryUnit, origClearingBusinessDate, strategyMarker, tradePublishIndicator, noTrdRegPublications, regulatoryReportType, correspondingPrice, consideration, deferredPublicationTime, copyMsgIndicator, some_bind] <;> rfl

structure AllocationReportAck where
  allocReportID : Terminated 1  -- tag 755
  allocID : Terminated 1  -- tag 70
  allocTransType : Terminated 1  -- tag 71
  allocStatus : Terminated 1  -- tag 87
  allocRejCode : Terminated 1  -- tag 88
  text : Option (Terminated 1)  -- tag 58

def AllocationReportAck.parts (record : AllocationReportAck) : List Part :=
  [Part.required [55, 53, 53] record.allocReportID,
   Part.required [55, 48] record.allocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [56, 55] record.allocStatus,
   Part.required [56, 56] record.allocRejCode,
   Part.optional [53, 56] record.text]

def AllocationReportAck.tags : List (List (List UInt8)) :=
  [[[55, 53, 53]], [[55, 48]], [[55, 49]], [[56, 55]], [[56, 56]], [[53, 56]]]

theorem AllocationReportAck.shape (record : AllocationReportAck) : record.parts.map Part.tags = AllocationReportAck.tags := rfl

def AllocationReportAck.decode (tokens : List Token) : Option AllocationReportAck := do
  let allocReportID ← readRequired [55, 53, 53] tokens
  let allocID ← readRequired [55, 48] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let allocRejCode ← readRequired [56, 56] tokens
  let text ← readOptional [53, 56] tokens
  pure { allocReportID, allocID, allocTransType, allocStatus, allocRejCode, text }

theorem AllocationReportAck.decode_agrees (record : AllocationReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationReportAck.decode tokens = some record := by
  have distinct : AllocationReportAck.tags.flatten.Nodup := by decide +kernel
  have allocReportID := readRequired_part [55, 53, 53] record.allocReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocRejCode := readRequired_part [56, 56] record.allocRejCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [AllocationReportAck.decode, allocReportID, allocID, allocTransType, allocStatus, allocRejCode, text, some_bind] <;> rfl

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

structure AllocationReport where
  allocReportID : Option (Terminated 1)  -- tag 755
  allocID : Option (Terminated 1)  -- tag 70
  secondaryAllocID : Terminated 1  -- tag 793
  allocTransType : Terminated 1  -- tag 71
  allocReportType : Terminated 1  -- tag 794
  allocStatus : Terminated 1  -- tag 87
  clearingBusinessDate : Option (Terminated 1)  -- tag 715
  side : Terminated 1  -- tag 54
  noExecs : List NoExecs  -- tag 124
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  quantity : Terminated 1  -- tag 53
  lastMkt : Option (Terminated 1)  -- tag 30
  avgPx : Terminated 1  -- tag 6
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradeDate : Terminated 1  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  noAllocs : List NoAllocs  -- tag 78
  text : Option (Terminated 1)  -- tag 58
  secondaryTradeID : Option (Terminated 1)  -- tag 1040
  origSecondaryTradeID : Option (Terminated 1)  -- tag 1127
  secondaryTrdType : Option (Terminated 1)  -- tag 855

def AllocationReport.parts (record : AllocationReport) : List Part :=
  [Part.optional [55, 53, 53] record.allocReportID,
   Part.optional [55, 48] record.allocID,
   Part.required [55, 57, 51] record.secondaryAllocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [55, 57, 52] record.allocReportType,
   Part.required [56, 55] record.allocStatus,
   Part.optional [55, 49, 53] record.clearingBusinessDate,
   Part.required [53, 52] record.side,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.required [53, 51] record.quantity,
   Part.optional [51, 48] record.lastMkt,
   Part.required [54] record.avgPx,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 52, 48] record.secondaryTradeID,
   Part.optional [49, 49, 50, 55] record.origSecondaryTradeID,
   Part.optional [56, 53, 53] record.secondaryTrdType]

def AllocationReport.tags : List (List (List UInt8)) :=
  [[[55, 53, 53]], [[55, 48]], [[55, 57, 51]], [[55, 49]], [[55, 57, 52]], [[56, 55]], [[55, 49, 53]], [[53, 52]], [49, 50, 52] :: NoExecs.members, [[53, 53]], [[52, 56]], [[50, 50]], [[53, 51]], [[51, 48]], [[54]], [52, 53, 51] :: NoPartyIDs.members, [[55, 53]], [[54, 48]], [55, 56] :: NoAllocs.members, [[53, 56]], [[49, 48, 52, 48]], [[49, 49, 50, 55]], [[56, 53, 53]]]

theorem AllocationReport.shape (record : AllocationReport) : record.parts.map Part.tags = AllocationReport.tags := rfl

def AllocationReport.decode (tokens : List Token) : Option AllocationReport := do
  let allocReportID ← readOptional [55, 53, 53] tokens
  let allocID ← readOptional [55, 48] tokens
  let secondaryAllocID ← readRequired [55, 57, 51] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let allocReportType ← readRequired [55, 57, 52] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let clearingBusinessDate ← readOptional [55, 49, 53] tokens
  let side ← readRequired [53, 52] tokens
  let noExecs ← readGroup [49, 50, 52] [51, 50] NoExecs.members NoExecs.decode tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let quantity ← readRequired [53, 51] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let avgPx ← readRequired [54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradeDate ← readRequired [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let noAllocs ← readGroup [55, 56] [55, 57] NoAllocs.members NoAllocs.decode tokens
  let text ← readOptional [53, 56] tokens
  let secondaryTradeID ← readOptional [49, 48, 52, 48] tokens
  let origSecondaryTradeID ← readOptional [49, 49, 50, 55] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  pure { allocReportID, allocID, secondaryAllocID, allocTransType, allocReportType, allocStatus, clearingBusinessDate, side, noExecs, symbol, securityID, securityIDSource, quantity, lastMkt, avgPx, noPartyIDs, tradeDate, transactTime, noAllocs, text, secondaryTradeID, origSecondaryTradeID, secondaryTrdType }

theorem AllocationReport.decode_agrees (record : AllocationReport) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationReport.decode tokens = some record := by
  have distinct : AllocationReport.tags.flatten.Nodup := by decide +kernel
  have allocReportID := readOptional_part [55, 53, 53] record.allocReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryAllocID := readRequired_part [55, 57, 51] record.secondaryAllocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocReportType := readRequired_part [55, 57, 52] record.allocReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingBusinessDate := readOptional_part [55, 49, 53] record.clearingBusinessDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [51, 50] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have quantity := readRequired_part [53, 51] record.quantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [55, 57] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have secondaryTradeID := readOptional_part [49, 48, 52, 48] record.secondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have origSecondaryTradeID := readOptional_part [49, 49, 50, 55] record.origSecondaryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [AllocationReport.decode, allocReportID, allocID, secondaryAllocID, allocTransType, allocReportType, allocStatus, clearingBusinessDate, side, noExecs, symbol, securityID, securityIDSource, quantity, lastMkt, avgPx, noPartyIDs, tradeDate, transactTime, noAllocs, text, secondaryTradeID, origSecondaryTradeID, secondaryTrdType, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | userResponse (header : Header) (r0 : UserResponse)
  | userNotification (header : Header) (r0 : UserNotification)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport)
  | listStatus (header : Header) (r0 : ListStatus)
  | massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement)
  | quoteRequestReject (header : Header) (r0 : QuoteRequestReject)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | quote (header : Header) (r0 : Quote)
  | quoteStatusReport (header : Header) (r0 : QuoteStatusReport)
  | oneSidedAuctionRequestAck (header : Header) (r0 : OneSidedAuctionRequestAck)
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | allocationReportAck (header : Header) (r0 : AllocationReportAck)
  | allocationReport (header : Header) (r0 : AllocationReport)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userNotification header r0 => ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionUpdateReport header r0 => ⟨[51, 53], ⟨[66, 80], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .listStatus header r0 => ⟨[51, 53], ⟨[78], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuoteAcknowledgement header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequestReject header r0 => ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quote header r0 => ⟨[51, 53], ⟨[83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteStatusReport header r0 => ⟨[51, 53], ⟨[65, 73], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .oneSidedAuctionRequestAck header r0 => ⟨[51, 53], ⟨[85, 68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationReportAck header r0 => ⟨[51, 53], ⟨[65, 84], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocationReport header r0 => ⟨[51, 53], ⟨[65, 83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
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
      else if token.value.val = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else if token.value.val = [67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value.val = [66, 80] then
        if known (Header.tags ++ SecurityDefinitionUpdateReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionUpdateReport.decode rest
          pure (.securityDefinitionUpdateReport header r0)
        else none
      else if token.value.val = [78] then
        if known (Header.tags ++ ListStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ListStatus.decode rest
          pure (.listStatus header r0)
        else none
      else if token.value.val = [98] then
        if known (Header.tags ++ MassQuoteAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuoteAcknowledgement.decode rest
          pure (.massQuoteAcknowledgement header r0)
        else none
      else if token.value.val = [65, 71] then
        if known (Header.tags ++ QuoteRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequestReject.decode rest
          pure (.quoteRequestReject header r0)
        else none
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
        else none
      else if token.value.val = [83] then
        if known (Header.tags ++ Quote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Quote.decode rest
          pure (.quote header r0)
        else none
      else if token.value.val = [65, 73] then
        if known (Header.tags ++ QuoteStatusReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteStatusReport.decode rest
          pure (.quoteStatusReport header r0)
        else none
      else if token.value.val = [85, 68] then
        if known (Header.tags ++ OneSidedAuctionRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OneSidedAuctionRequestAck.decode rest
          pure (.oneSidedAuctionRequestAck header r0)
        else none
      else if token.value.val = [65, 82] then
        if known (Header.tags ++ TradeCaptureReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportAck.decode rest
          pure (.tradeCaptureReportAck header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [65, 84] then
        if known (Header.tags ++ AllocationReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationReportAck.decode rest
          pure (.allocationReportAck header r0)
        else none
      else if token.value.val = [65, 83] then
        if known (Header.tags ++ AllocationReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationReport.decode rest
          pure (.allocationReport header r0)
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

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
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

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport) :
    Message.decode (Message.tokens (.securityDefinitionUpdateReport header r0)) = some (.securityDefinitionUpdateReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionUpdateReport.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionUpdateReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionUpdateReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionUpdateReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_listStatus (header : Header) (r0 : ListStatus) :
    Message.decode (Message.tokens (.listStatus header r0)) = some (.listStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ListStatus.tags) rfl rfl (by decide +kernel))
  have c1 := ListStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ListStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ListStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decode (Message.tokens (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuoteAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decode (Message.tokens (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quote (header : Header) (r0 : Quote) :
    Message.decode (Message.tokens (.quote header r0)) = some (.quote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) rfl rfl (by decide +kernel))
  have c1 := Quote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Quote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decode (Message.tokens (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteStatusReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_oneSidedAuctionRequestAck (header : Header) (r0 : OneSidedAuctionRequestAck) :
    Message.decode (Message.tokens (.oneSidedAuctionRequestAck header r0)) = some (.oneSidedAuctionRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedAuctionRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := OneSidedAuctionRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OneSidedAuctionRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OneSidedAuctionRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decode (Message.tokens (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationReportAck (header : Header) (r0 : AllocationReportAck) :
    Message.decode (Message.tokens (.allocationReportAck header r0)) = some (.allocationReportAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReportAck.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReportAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationReportAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocationReport (header : Header) (r0 : AllocationReport) :
    Message.decode (Message.tokens (.allocationReport header r0)) = some (.allocationReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReport.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0
  | userNotification header r0 => exact Message.decode_userNotification header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decode_securityDefinitionUpdateReport header r0
  | listStatus header r0 => exact Message.decode_listStatus header r0
  | massQuoteAcknowledgement header r0 => exact Message.decode_massQuoteAcknowledgement header r0
  | quoteRequestReject header r0 => exact Message.decode_quoteRequestReject header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | quote header r0 => exact Message.decode_quote header r0
  | quoteStatusReport header r0 => exact Message.decode_quoteStatusReport header r0
  | oneSidedAuctionRequestAck header r0 => exact Message.decode_oneSidedAuctionRequestAck header r0
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | allocationReportAck header r0 => exact Message.decode_allocationReportAck header r0
  | allocationReport header r0 => exact Message.decode_allocationReport header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

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

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[67, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_securityDefinitionUpdateReport (header : Header) (r0 : SecurityDefinitionUpdateReport) :
    Message.decodeBytes (Message.encode (.securityDefinitionUpdateReport header r0)) = some (.securityDefinitionUpdateReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 80], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionUpdateReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionUpdateReport header r0

theorem Message.decodeBytes_listStatus (header : Header) (r0 : ListStatus) :
    Message.decodeBytes (Message.encode (.listStatus header r0)) = some (.listStatus header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[78], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ListStatus.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_listStatus header r0

theorem Message.decodeBytes_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decodeBytes (Message.encode (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[98], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuoteAcknowledgement header r0

theorem Message.decodeBytes_quoteRequestReject (header : Header) (r0 : QuoteRequestReject) :
    Message.decodeBytes (Message.encode (.quoteRequestReject header r0)) = some (.quoteRequestReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequestReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequestReject header r0

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

theorem Message.decodeBytes_quote (header : Header) (r0 : Quote) :
    Message.decodeBytes (Message.encode (.quote header r0)) = some (.quote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Quote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quote header r0

theorem Message.decodeBytes_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decodeBytes (Message.encode (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 73], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteStatusReport header r0

theorem Message.decodeBytes_oneSidedAuctionRequestAck (header : Header) (r0 : OneSidedAuctionRequestAck) :
    Message.decodeBytes (Message.encode (.oneSidedAuctionRequestAck header r0)) = some (.oneSidedAuctionRequestAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OneSidedAuctionRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oneSidedAuctionRequestAck header r0

theorem Message.decodeBytes_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_allocationReportAck (header : Header) (r0 : AllocationReportAck) :
    Message.decodeBytes (Message.encode (.allocationReportAck header r0)) = some (.allocationReportAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 84], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationReportAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationReportAck header r0

theorem Message.decodeBytes_allocationReport (header : Header) (r0 : AllocationReport) :
    Message.decodeBytes (Message.encode (.allocationReport header r0)) = some (.allocationReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | securityDefinitionUpdateReport header r0 => exact Message.decodeBytes_securityDefinitionUpdateReport header r0
  | listStatus header r0 => exact Message.decodeBytes_listStatus header r0
  | massQuoteAcknowledgement header r0 => exact Message.decodeBytes_massQuoteAcknowledgement header r0
  | quoteRequestReject header r0 => exact Message.decodeBytes_quoteRequestReject header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | quote header r0 => exact Message.decodeBytes_quote header r0
  | quoteStatusReport header r0 => exact Message.decodeBytes_quoteStatusReport header r0
  | oneSidedAuctionRequestAck header r0 => exact Message.decodeBytes_oneSidedAuctionRequestAck header r0
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | allocationReportAck header r0 => exact Message.decodeBytes_allocationReportAck header r0
  | allocationReport header r0 => exact Message.decodeBytes_allocationReport header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNordicderivativesOrderentryFixV223Exchange
