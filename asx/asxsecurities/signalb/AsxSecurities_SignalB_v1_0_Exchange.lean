import Wire

/-!
# Australian Securities Exchange Signal B v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxsecuritiesSignalbFixV10Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122
  applVerID : Option (Terminated 1)  -- tag 1128

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 50, 56] record.applVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]], [[49, 49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, applVerID }

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
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, applVerID, some_bind] <;> rfl

structure Logon where
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  nextExpectedMsgSeqNum : Option (Terminated 1)  -- tag 789
  username : Option (Terminated 1)  -- tag 553
  password : Option (Terminated 1)  -- tag 554
  newPassword : Option (Terminated 1)  -- tag 925
  sessionStatus : Option (Terminated 1)  -- tag 1409
  defaultApplVerID : Option (Terminated 1)  -- tag 1137
  text : Option (Terminated 1)  -- tag 58

def Logon.parts (record : Logon) : List Part :=
  [Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.optional [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password,
   Part.optional [57, 50, 53] record.newPassword,
   Part.optional [49, 52, 48, 57] record.sessionStatus,
   Part.optional [49, 49, 51, 55] record.defaultApplVerID,
   Part.optional [53, 56] record.text]

def Logon.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]], [[49, 52, 49]], [[55, 56, 57]], [[53, 53, 51]], [[53, 53, 52]], [[57, 50, 53]], [[49, 52, 48, 57]], [[49, 49, 51, 55]], [[53, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let nextExpectedMsgSeqNum ← readOptional [55, 56, 57] tokens
  let username ← readOptional [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  let newPassword ← readOptional [57, 50, 53] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  let defaultApplVerID ← readOptional [49, 49, 51, 55] tokens
  let text ← readOptional [53, 56] tokens
  pure { heartBtInt, resetSeqNumFlag, nextExpectedMsgSeqNum, username, password, newPassword, sessionStatus, defaultApplVerID, text }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nextExpectedMsgSeqNum := readOptional_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have username := readOptional_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have newPassword := readOptional_part [57, 50, 53] record.newPassword tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have defaultApplVerID := readOptional_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Logon.decode, heartBtInt, resetSeqNumFlag, nextExpectedMsgSeqNum, username, password, newPassword, sessionStatus, defaultApplVerID, text, some_bind] <;> rfl

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

structure TradeCaptureReportRequestAck where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  tradeRequestResult : Option (Terminated 1)  -- tag 749
  tradeRequestStatus : Option (Terminated 1)  -- tag 750
  text : Option (Terminated 1)  -- tag 58

def TradeCaptureReportRequestAck.parts (record : TradeCaptureReportRequestAck) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [55, 52, 57] record.tradeRequestResult,
   Part.optional [55, 53, 48] record.tradeRequestStatus,
   Part.optional [53, 56] record.text]

def TradeCaptureReportRequestAck.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[55, 52, 57]], [[55, 53, 48]], [[53, 56]]]

theorem TradeCaptureReportRequestAck.shape (record : TradeCaptureReportRequestAck) : record.parts.map Part.tags = TradeCaptureReportRequestAck.tags := rfl

def TradeCaptureReportRequestAck.decode (tokens : List Token) : Option TradeCaptureReportRequestAck := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let tradeRequestResult ← readOptional [55, 52, 57] tokens
  let tradeRequestStatus ← readOptional [55, 53, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { tradeRequestID, tradeRequestType, tradeRequestResult, tradeRequestStatus, text }

theorem TradeCaptureReportRequestAck.decode_agrees (record : TradeCaptureReportRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequestAck.decode tokens = some record := by
  have distinct : TradeCaptureReportRequestAck.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeRequestResult := readOptional_part [55, 52, 57] record.tradeRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeRequestStatus := readOptional_part [55, 53, 48] record.tradeRequestStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReportRequestAck.decode, tradeRequestID, tradeRequestType, tradeRequestResult, tradeRequestStatus, text, some_bind] <;> rfl

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

structure NoClearingInstructions where
  clearingInstruction : Terminated 1  -- tag 577

def NoClearingInstructions.parts (record : NoClearingInstructions) : List Part :=
  [Part.required [53, 55, 55] record.clearingInstruction]

def NoClearingInstructions.tags : List (List (List UInt8)) :=
  [[[53, 55, 55]]]

theorem NoClearingInstructions.shape (record : NoClearingInstructions) : record.parts.map Part.tags = NoClearingInstructions.tags := rfl

def NoClearingInstructions.decode (tokens : List Token) : Option NoClearingInstructions := do
  let clearingInstruction ← readRequired [53, 55, 55] tokens
  pure { clearingInstruction }

theorem NoClearingInstructions.decode_agrees (record : NoClearingInstructions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoClearingInstructions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoClearingInstructions.decode tokens = some record := by
  have distinct : NoClearingInstructions.tags.flatten.Nodup := by decide +kernel
  have clearingInstruction := readRequired_part [53, 55, 55] record.clearingInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoClearingInstructions.decode, clearingInstruction, some_bind] <;> rfl

def NoClearingInstructions.members : List (List UInt8) := NoClearingInstructions.tags.flatten

def NoClearingInstructions.encode (entry : NoClearingInstructions) : List Token := encodeParts entry.parts

theorem NoClearingInstructions.decode_encode (entry : NoClearingInstructions) : NoClearingInstructions.decode entry.encode = some entry :=
  NoClearingInstructions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoClearingInstructions.within (entry : NoClearingInstructions) : ∀ token ∈ entry.encode, token.tag ∈ NoClearingInstructions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoClearingInstructions.shape] at this

theorem NoClearingInstructions.led (entry : NoClearingInstructions) : Lead [53, 55, 55] entry.encode :=
  lead_parts [53, 55, 55] entry.clearingInstruction _ NoClearingInstructions.tags.tail rfl (by decide +kernel)

structure NoSides where
  side : Terminated 1  -- tag 54
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Option (Terminated 1)  -- tag 11
  noClearingInstructions : List NoClearingInstructions  -- tag 576

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [49] record.account,
   Part.optional [49, 49] record.clOrdID,
   Part.group [53, 55, 54] NoClearingInstructions.members NoClearingInstructions.encode NoClearingInstructions.within record.noClearingInstructions]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [52, 53, 51] :: NoPartyIDs.members, [[49]], [[49, 49]], [53, 55, 54] :: NoClearingInstructions.members]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readOptional [49] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let noClearingInstructions ← readGroup [53, 55, 54] [53, 55, 55] NoClearingInstructions.members NoClearingInstructions.decode tokens
  pure { side, noPartyIDs, account, clOrdID, noClearingInstructions }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noClearingInstructions := readGroup_part [53, 55, 54] [53, 55, 55] NoClearingInstructions.members NoClearingInstructions.encode NoClearingInstructions.within NoClearingInstructions.decode NoClearingInstructions.decode_encode NoClearingInstructions.led record.noClearingInstructions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NoSides.decode, side, noPartyIDs, account, clOrdID, noClearingInstructions, some_bind] <;> rfl

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
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  origTradeDate : Option (Terminated 1)  -- tag 1125
  trdConditionCode : Option (Terminated 1)  -- tag 20003
  corporateActionCode : Option (Terminated 1)  -- tag 20007
  trdMatchID : Option (Terminated 1)  -- tag 880
  tradeID : Terminated 1  -- tag 1003
  tradeDate : Terminated 1  -- tag 75
  settlDate : Option (Terminated 1)  -- tag 64
  transactTime : Option (Terminated 1)  -- tag 60
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  grossTradeAmt : Option (Terminated 1)  -- tag 381
  currency : Option (Terminated 1)  -- tag 15
  asOfIndicator : Option (Terminated 1)  -- tag 1015
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  securityIDSource : Option (Terminated 1)  -- tag 22
  securityID : Option (Terminated 1)  -- tag 48
  symbol : Option (Terminated 1)  -- tag 55
  cFICode : Option (Terminated 1)  -- tag 461
  marketID : Option (Terminated 1)  -- tag 1301
  issuer : Option (Terminated 1)  -- tag 106
  noSides : List NoSides  -- tag 552

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [49, 49, 50, 53] record.origTradeDate,
   Part.optional [50, 48, 48, 48, 51] record.trdConditionCode,
   Part.optional [50, 48, 48, 48, 55] record.corporateActionCode,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.required [49, 48, 48, 51] record.tradeID,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 52] record.settlDate,
   Part.optional [54, 48] record.transactTime,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [51, 56, 49] record.grossTradeAmt,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 48, 49, 53] record.asOfIndicator,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 54, 49] record.cFICode,
   Part.optional [49, 51, 48, 49] record.marketID,
   Part.optional [49, 48, 54] record.issuer,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[52, 56, 55]], [[49, 49, 50, 53]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 48, 55]], [[56, 56, 48]], [[49, 48, 48, 51]], [[55, 53]], [[54, 52]], [[54, 48]], [[51, 50]], [[51, 49]], [[51, 56, 49]], [[49, 53]], [[49, 48, 49, 53]], [[49, 54, 55]], [[55, 54, 50]], [[50, 50]], [[52, 56]], [[53, 53]], [[52, 54, 49]], [[49, 51, 48, 49]], [[49, 48, 54]], [53, 53, 50] :: NoSides.members]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let origTradeDate ← readOptional [49, 49, 50, 53] tokens
  let trdConditionCode ← readOptional [50, 48, 48, 48, 51] tokens
  let corporateActionCode ← readOptional [50, 48, 48, 48, 55] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let settlDate ← readOptional [54, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let grossTradeAmt ← readOptional [51, 56, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let asOfIndicator ← readOptional [49, 48, 49, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let cFICode ← readOptional [52, 54, 49] tokens
  let marketID ← readOptional [49, 51, 48, 49] tokens
  let issuer ← readOptional [49, 48, 54] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  pure { tradeReportTransType, origTradeDate, trdConditionCode, corporateActionCode, trdMatchID, tradeID, tradeDate, settlDate, transactTime, lastShares, lastPx, grossTradeAmt, currency, asOfIndicator, securityType, securitySubType, securityIDSource, securityID, symbol, cFICode, marketID, issuer, noSides }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origTradeDate := readOptional_part [49, 49, 50, 53] record.origTradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have trdConditionCode := readOptional_part [50, 48, 48, 48, 51] record.trdConditionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have corporateActionCode := readOptional_part [50, 48, 48, 48, 55] record.corporateActionCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have grossTradeAmt := readOptional_part [51, 56, 49] record.grossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have asOfIndicator := readOptional_part [49, 48, 49, 53] record.asOfIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cFICode := readOptional_part [52, 54, 49] record.cFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have marketID := readOptional_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have issuer := readOptional_part [49, 48, 54] record.issuer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportTransType, origTradeDate, trdConditionCode, corporateActionCode, trdMatchID, tradeID, tradeDate, settlDate, transactTime, lastShares, lastPx, grossTradeAmt, currency, asOfIndicator, securityType, securitySubType, securityIDSource, securityID, symbol, cFICode, marketID, issuer, noSides, some_bind] <;> rfl

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

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequestAck header r0 => ⟨[51, 53], ⟨[65, 81], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
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
      else if token.value.val = [65, 81] then
        if known (Header.tags ++ TradeCaptureReportRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequestAck.decode rest
          pure (.tradeCaptureReportRequestAck header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
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

theorem Message.decode_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decode (Message.tokens (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decode_tradeCaptureReportRequestAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0

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

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[48], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

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

theorem Message.decodeBytes_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 81], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequestAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequestAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decodeBytes_tradeCaptureReportRequestAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AsxAsxsecuritiesSignalbFixV10Exchange
