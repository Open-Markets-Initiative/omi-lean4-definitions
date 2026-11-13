import Wire

/-!
# Eurex Exchange Cash Order Entry v15.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.EurexT7CashorderentryFixV150Client

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 50]], [[53, 54]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, possResend, origSendingTime }

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
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, possResend, origSendingTime, some_bind] <;> rfl

structure NoRootPartyIDs where
  rootPartyID : Terminated 1  -- tag 1117
  rootPartyIDSource : Terminated 1  -- tag 1118
  rootPartyRole : Terminated 1  -- tag 1119

def NoRootPartyIDs.parts (record : NoRootPartyIDs) : List Part :=
  [Part.required [49, 49, 49, 55] record.rootPartyID,
   Part.required [49, 49, 49, 56] record.rootPartyIDSource,
   Part.required [49, 49, 49, 57] record.rootPartyRole]

def NoRootPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 49, 49, 55]], [[49, 49, 49, 56]], [[49, 49, 49, 57]]]

theorem NoRootPartyIDs.shape (record : NoRootPartyIDs) : record.parts.map Part.tags = NoRootPartyIDs.tags := rfl

def NoRootPartyIDs.decode (tokens : List Token) : Option NoRootPartyIDs := do
  let rootPartyID ← readRequired [49, 49, 49, 55] tokens
  let rootPartyIDSource ← readRequired [49, 49, 49, 56] tokens
  let rootPartyRole ← readRequired [49, 49, 49, 57] tokens
  pure { rootPartyID, rootPartyIDSource, rootPartyRole }

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
  simp only [NoRootPartyIDs.decode, rootPartyID, rootPartyIDSource, rootPartyRole, some_bind] <;> rfl

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

structure CrossRequest where
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  currency : Option (Terminated 1)  -- tag 15
  orderQty : Terminated 1  -- tag 38
  crossRequestID : Terminated 1  -- tag 2672

def CrossRequest.parts (record : CrossRequest) : List Part :=
  [Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.optional [49, 53] record.currency,
   Part.required [51, 56] record.orderQty,
   Part.required [50, 54, 55, 50] record.crossRequestID]

def CrossRequest.tags : List (List (List UInt8)) :=
  [[49, 49, 49, 54] :: NoRootPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[49, 53]], [[51, 56]], [[50, 54, 55, 50]]]

theorem CrossRequest.shape (record : CrossRequest) : record.parts.map Part.tags = CrossRequest.tags := rfl

def CrossRequest.decode (tokens : List Token) : Option CrossRequest := do
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let orderQty ← readRequired [51, 56] tokens
  let crossRequestID ← readRequired [50, 54, 55, 50] tokens
  pure { noRootPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, orderQty, crossRequestID }

theorem CrossRequest.decode_agrees (record : CrossRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ CrossRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CrossRequest.decode tokens = some record := by
  have distinct : CrossRequest.tags.flatten.Nodup := by decide +kernel
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have crossRequestID := readRequired_part [50, 54, 55, 50] record.crossRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [CrossRequest.decode, noRootPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, orderQty, crossRequestID, some_bind] <;> rfl

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
  password : Option (Terminated 1)  -- tag 554
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  defaultCstmApplVerID : Terminated 1  -- tag 1408
  defaultCstmApplVerSubID : Option (Terminated 1)  -- tag 28763
  tradSesMode : Option (Terminated 1)  -- tag 339
  throttleInst : Terminated 1  -- tag 1685
  throttleMaxQueueTime : Option (Terminated 1)  -- tag 28790

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [53, 53, 52] record.password,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.required [49, 52, 48, 56] record.defaultCstmApplVerID,
   Part.optional [50, 56, 55, 54, 51] record.defaultCstmApplVerSubID,
   Part.optional [51, 51, 57] record.tradSesMode,
   Part.required [49, 54, 56, 53] record.throttleInst,
   Part.optional [50, 56, 55, 57, 48] record.throttleMaxQueueTime]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[53, 53, 52]], [[49, 52, 49]], [[49, 52, 48, 56]], [[50, 56, 55, 54, 51]], [[51, 51, 57]], [[49, 54, 56, 53]], [[50, 56, 55, 57, 48]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let password ← readOptional [53, 53, 52] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let defaultCstmApplVerID ← readRequired [49, 52, 48, 56] tokens
  let defaultCstmApplVerSubID ← readOptional [50, 56, 55, 54, 51] tokens
  let tradSesMode ← readOptional [51, 51, 57] tokens
  let throttleInst ← readRequired [49, 54, 56, 53] tokens
  let throttleMaxQueueTime ← readOptional [50, 56, 55, 57, 48] tokens
  pure { encryptMethod, heartBtInt, password, resetSeqNumFlag, defaultCstmApplVerID, defaultCstmApplVerSubID, tradSesMode, throttleInst, throttleMaxQueueTime }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have defaultCstmApplVerID := readRequired_part [49, 52, 48, 56] record.defaultCstmApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have defaultCstmApplVerSubID := readOptional_part [50, 56, 55, 54, 51] record.defaultCstmApplVerSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradSesMode := readOptional_part [51, 51, 57] record.tradSesMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have throttleInst := readRequired_part [49, 54, 56, 53] record.throttleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have throttleMaxQueueTime := readOptional_part [50, 56, 55, 57, 48] record.throttleMaxQueueTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, password, resetSeqNumFlag, defaultCstmApplVerID, defaultCstmApplVerSubID, tradSesMode, throttleInst, throttleMaxQueueTime, some_bind] <;> rfl

structure Logout where
  text : Option (Terminated 1)  -- tag 58
  sessionStatus : Option (Terminated 1)  -- tag 1409

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.optional [49, 52, 48, 57] record.sessionStatus]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[49, 52, 48, 57]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  pure { text, sessionStatus }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, text, sessionStatus, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376
  noPartySubIDs : Option (Terminated 1)  -- tag 802
  partySubID : Option (Terminated 1)  -- tag 523
  partySubIDType : Option (Terminated 1)  -- tag 803

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier,
   Part.optional [56, 48, 50] record.noPartySubIDs,
   Part.optional [53, 50, 51] record.partySubID,
   Part.optional [56, 48, 51] record.partySubIDType]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[56, 48, 50]], [[53, 50, 51]], [[56, 48, 51]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  let noPartySubIDs ← readOptional [56, 48, 50] tokens
  let partySubID ← readOptional [53, 50, 51] tokens
  let partySubIDType ← readOptional [56, 48, 51] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier, noPartySubIDs, partySubID, partySubIDType }

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
  have noPartySubIDs := readOptional_part [56, 48, 50] record.noPartySubIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partySubID := readOptional_part [53, 50, 51] record.partySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partySubIDType := readOptional_part [56, 48, 51] record.partySubIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, partyRoleQualifier, noPartySubIDs, partySubID, partySubIDType, some_bind] <;> rfl

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
  tradingSessionSubID : Terminated 1  -- tag 625

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID,
   Part.required [54, 50, 53] record.tradingSessionSubID]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]], [[54, 50, 53]]]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let tradingSessionSubID ← readRequired [54, 50, 53] tokens
  pure { tradingSessionID, tradingSessionSubID }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradingSessionSubID := readRequired_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, tradingSessionSubID, some_bind] <;> rfl

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

structure NoMatchInst where
  matchInst : Terminated 1  -- tag 1625
  matchInstCrossID : Terminated 1  -- tag 28744

def NoMatchInst.parts (record : NoMatchInst) : List Part :=
  [Part.required [49, 54, 50, 53] record.matchInst,
   Part.required [50, 56, 55, 52, 52] record.matchInstCrossID]

def NoMatchInst.tags : List (List (List UInt8)) :=
  [[[49, 54, 50, 53]], [[50, 56, 55, 52, 52]]]

theorem NoMatchInst.shape (record : NoMatchInst) : record.parts.map Part.tags = NoMatchInst.tags := rfl

def NoMatchInst.decode (tokens : List Token) : Option NoMatchInst := do
  let matchInst ← readRequired [49, 54, 50, 53] tokens
  let matchInstCrossID ← readRequired [50, 56, 55, 52, 52] tokens
  pure { matchInst, matchInstCrossID }

theorem NoMatchInst.decode_agrees (record : NoMatchInst) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchInst.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchInst.decode tokens = some record := by
  have distinct : NoMatchInst.tags.flatten.Nodup := by decide +kernel
  have matchInst := readRequired_part [49, 54, 50, 53] record.matchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchInstCrossID := readRequired_part [50, 56, 55, 52, 52] record.matchInstCrossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoMatchInst.decode, matchInst, matchInstCrossID, some_bind] <;> rfl

def NoMatchInst.members : List (List UInt8) := NoMatchInst.tags.flatten

def NoMatchInst.encode (entry : NoMatchInst) : List Token := encodeParts entry.parts

theorem NoMatchInst.decode_encode (entry : NoMatchInst) : NoMatchInst.decode entry.encode = some entry :=
  NoMatchInst.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchInst.within (entry : NoMatchInst) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchInst.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchInst.shape] at this

theorem NoMatchInst.led (entry : NoMatchInst) : Lead [49, 54, 50, 53] entry.encode :=
  lead_parts [49, 54, 50, 53] entry.matchInst _ NoMatchInst.tags.tail rfl (by decide +kernel)

structure NoOrderAttributes where
  orderAttributeType : Terminated 1  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595

def NoOrderAttributes.parts (record : NoOrderAttributes) : List Part :=
  [Part.required [50, 53, 57, 52] record.orderAttributeType,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue]

def NoOrderAttributes.tags : List (List (List UInt8)) :=
  [[[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem NoOrderAttributes.shape (record : NoOrderAttributes) : record.parts.map Part.tags = NoOrderAttributes.tags := rfl

def NoOrderAttributes.decode (tokens : List Token) : Option NoOrderAttributes := do
  let orderAttributeType ← readRequired [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  pure { orderAttributeType, orderAttributeValue }

theorem NoOrderAttributes.decode_agrees (record : NoOrderAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderAttributes.decode tokens = some record := by
  have distinct : NoOrderAttributes.tags.flatten.Nodup := by decide +kernel
  have orderAttributeType := readRequired_part [50, 53, 57, 52] record.orderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
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

structure NoValueChecks where
  valueCheckType : Terminated 1  -- tag 1869
  valueCheckAction : Terminated 1  -- tag 1870

def NoValueChecks.parts (record : NoValueChecks) : List Part :=
  [Part.required [49, 56, 54, 57] record.valueCheckType,
   Part.required [49, 56, 55, 48] record.valueCheckAction]

def NoValueChecks.tags : List (List (List UInt8)) :=
  [[[49, 56, 54, 57]], [[49, 56, 55, 48]]]

theorem NoValueChecks.shape (record : NoValueChecks) : record.parts.map Part.tags = NoValueChecks.tags := rfl

def NoValueChecks.decode (tokens : List Token) : Option NoValueChecks := do
  let valueCheckType ← readRequired [49, 56, 54, 57] tokens
  let valueCheckAction ← readRequired [49, 56, 55, 48] tokens
  pure { valueCheckType, valueCheckAction }

theorem NoValueChecks.decode_agrees (record : NoValueChecks) (tokens : List Token)
    (agrees : ∀ tags ∈ NoValueChecks.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoValueChecks.decode tokens = some record := by
  have distinct : NoValueChecks.tags.flatten.Nodup := by decide +kernel
  have valueCheckType := readRequired_part [49, 56, 54, 57] record.valueCheckType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have valueCheckAction := readRequired_part [49, 56, 55, 48] record.valueCheckAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoValueChecks.decode, valueCheckType, valueCheckAction, some_bind] <;> rfl

def NoValueChecks.members : List (List UInt8) := NoValueChecks.tags.flatten

def NoValueChecks.encode (entry : NoValueChecks) : List Token := encodeParts entry.parts

theorem NoValueChecks.decode_encode (entry : NoValueChecks) : NoValueChecks.decode entry.encode = some entry :=
  NoValueChecks.decode_agrees entry _ (fun _ _ => rfl)

theorem NoValueChecks.within (entry : NoValueChecks) : ∀ token ∈ entry.encode, token.tag ∈ NoValueChecks.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoValueChecks.shape] at this

theorem NoValueChecks.led (entry : NoValueChecks) : Lead [49, 56, 54, 57] entry.encode :=
  lead_parts [49, 56, 54, 57] entry.valueCheckType _ NoValueChecks.tags.tail rfl (by decide +kernel)

structure NewOrderSingle where
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  noTradingSessions : List NoTradingSessions  -- tag 386
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  pegOffsetType : Option (Terminated 1)  -- tag 836
  noMatchInst : List NoMatchInst  -- tag 1624
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMethod : Option (Terminated 1)  -- tag 1084
  displayLowQty : Option (Terminated 1)  -- tag 1085
  displayHighQty : Option (Terminated 1)  -- tag 1086
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  noValueChecks : List NoValueChecks  -- tag 1868
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  minQty : Option (Terminated 1)  -- tag 110
  ordType : Terminated 1  -- tag 40
  midPointType : Option (Terminated 1)  -- tag 30388
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  freeText1 : Option (Terminated 1)  -- tag 25007
  timeInForce : Option (Terminated 1)  -- tag 59
  stopPx : Option (Terminated 1)  -- tag 99
  quoteID : Option (Terminated 1)  -- tag 117
  brokerInternalizationID : Option (Terminated 1)  -- tag 25263
  expireDate : Option (Terminated 1)  -- tag 432
  orderOrigination : Option (Terminated 1)  -- tag 1724
  tradingCapacity : Terminated 1  -- tag 1815
  crossMatchInstruction : Option (Terminated 1)  -- tag 31625
  freeText2 : Option (Terminated 1)  -- tag 25008
  freeText4 : Option (Terminated 1)  -- tag 25107
  tradeAtCloseOptIn : Option (Terminated 1)  -- tag 30625

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [56, 51, 54] record.pegOffsetType,
   Part.group [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within record.noMatchInst,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 52] record.displayMethod,
   Part.optional [49, 48, 56, 53] record.displayLowQty,
   Part.optional [49, 48, 56, 54] record.displayHighQty,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.group [49, 56, 54, 56] NoValueChecks.members NoValueChecks.encode NoValueChecks.within record.noValueChecks,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [52, 48] record.ordType,
   Part.optional [51, 48, 51, 56, 56] record.midPointType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.optional [50, 53, 48, 48, 55] record.freeText1,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 55] record.quoteID,
   Part.optional [50, 53, 50, 54, 51] record.brokerInternalizationID,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [51, 49, 54, 50, 53] record.crossMatchInstruction,
   Part.optional [50, 53, 48, 48, 56] record.freeText2,
   Part.optional [50, 53, 49, 48, 55] record.freeText4,
   Part.optional [51, 48, 54, 50, 53] record.tradeAtCloseOptIn]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [51, 56, 54] :: NoTradingSessions.members, [[50, 49, 49]], [[56, 51, 54]], [49, 54, 50, 52] :: NoMatchInst.members, [[49, 49, 51, 56]], [[49, 48, 56, 52]], [[49, 48, 56, 53]], [[49, 48, 56, 54]], [50, 53, 57, 51] :: NoOrderAttributes.members, [49, 56, 54, 56] :: NoValueChecks.members, [[49, 49]], [[49, 53]], [[49, 56]], [[51, 56]], [[49, 49, 48]], [[52, 48]], [[51, 48, 51, 56, 56]], [[52, 52]], [[53, 52]], [[50, 53, 48, 48, 55]], [[53, 57]], [[57, 57]], [[49, 49, 55]], [[50, 53, 50, 54, 51]], [[52, 51, 50]], [[49, 55, 50, 52]], [[49, 56, 49, 53]], [[51, 49, 54, 50, 53]], [[50, 53, 48, 48, 56]], [[50, 53, 49, 48, 55]], [[51, 48, 54, 50, 53]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let pegOffsetType ← readOptional [56, 51, 54] tokens
  let noMatchInst ← readGroup [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.decode tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMethod ← readOptional [49, 48, 56, 52] tokens
  let displayLowQty ← readOptional [49, 48, 56, 53] tokens
  let displayHighQty ← readOptional [49, 48, 56, 54] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let noValueChecks ← readGroup [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.decode tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let ordType ← readRequired [52, 48] tokens
  let midPointType ← readOptional [51, 48, 51, 56, 56] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let freeText1 ← readOptional [50, 53, 48, 48, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let quoteID ← readOptional [49, 49, 55] tokens
  let brokerInternalizationID ← readOptional [50, 53, 50, 54, 51] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let crossMatchInstruction ← readOptional [51, 49, 54, 50, 53] tokens
  let freeText2 ← readOptional [50, 53, 48, 48, 56] tokens
  let freeText4 ← readOptional [50, 53, 49, 48, 55] tokens
  let tradeAtCloseOptIn ← readOptional [51, 48, 54, 50, 53] tokens
  pure { noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noTradingSessions, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderAttributes, noValueChecks, clOrdID, currency, execInst, orderQty, minQty, ordType, midPointType, price, side, freeText1, timeInForce, stopPx, quoteID, brokerInternalizationID, expireDate, orderOrigination, tradingCapacity, crossMatchInstruction, freeText2, freeText4, tradeAtCloseOptIn }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have pegOffsetType := readOptional_part [56, 51, 54] record.pegOffsetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noMatchInst := readGroup_part [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.encode NoMatchInst.within NoMatchInst.decode NoMatchInst.decode_encode NoMatchInst.led record.noMatchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have displayMethod := readOptional_part [49, 48, 56, 52] record.displayMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have displayLowQty := readOptional_part [49, 48, 56, 53] record.displayLowQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have displayHighQty := readOptional_part [49, 48, 56, 54] record.displayHighQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noValueChecks := readGroup_part [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.encode NoValueChecks.within NoValueChecks.decode NoValueChecks.decode_encode NoValueChecks.led record.noValueChecks tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have midPointType := readOptional_part [51, 48, 51, 56, 56] record.midPointType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have freeText1 := readOptional_part [50, 53, 48, 48, 55] record.freeText1 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have brokerInternalizationID := readOptional_part [50, 53, 50, 54, 51] record.brokerInternalizationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have crossMatchInstruction := readOptional_part [51, 49, 54, 50, 53] record.crossMatchInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have freeText2 := readOptional_part [50, 53, 48, 48, 56] record.freeText2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have freeText4 := readOptional_part [50, 53, 49, 48, 55] record.freeText4 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have tradeAtCloseOptIn := readOptional_part [51, 48, 54, 50, 53] record.tradeAtCloseOptIn tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  simp only [NewOrderSingle.decode, noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noTradingSessions, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderAttributes, noValueChecks, clOrdID, currency, execInst, orderQty, minQty, ordType, midPointType, price, side, freeText1, timeInForce, stopPx, quoteID, brokerInternalizationID, expireDate, orderOrigination, tradingCapacity, crossMatchInstruction, freeText2, freeText4, tradeAtCloseOptIn, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  noTradingSessions : List NoTradingSessions  -- tag 386
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  pegOffsetType : Option (Terminated 1)  -- tag 836
  noMatchInst : List NoMatchInst  -- tag 1624
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMethod : Option (Terminated 1)  -- tag 1084
  displayLowQty : Option (Terminated 1)  -- tag 1085
  displayHighQty : Option (Terminated 1)  -- tag 1086
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  noValueChecks : List NoValueChecks  -- tag 1868
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  minQty : Option (Terminated 1)  -- tag 110
  ordType : Terminated 1  -- tag 40
  midPointType : Option (Terminated 1)  -- tag 30388
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  freeText1 : Option (Terminated 1)  -- tag 25007
  timeInForce : Option (Terminated 1)  -- tag 59
  stopPx : Option (Terminated 1)  -- tag 99
  brokerInternalizationID : Option (Terminated 1)  -- tag 25263
  expireDate : Option (Terminated 1)  -- tag 432
  orderOrigination : Option (Terminated 1)  -- tag 1724
  tradingCapacity : Terminated 1  -- tag 1815
  crossMatchInstruction : Option (Terminated 1)  -- tag 31625
  freeText2 : Option (Terminated 1)  -- tag 25008
  freeText4 : Option (Terminated 1)  -- tag 25107

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [56, 51, 54] record.pegOffsetType,
   Part.group [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within record.noMatchInst,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 52] record.displayMethod,
   Part.optional [49, 48, 56, 53] record.displayLowQty,
   Part.optional [49, 48, 56, 54] record.displayHighQty,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.group [49, 56, 54, 56] NoValueChecks.members NoValueChecks.encode NoValueChecks.within record.noValueChecks,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [52, 48] record.ordType,
   Part.optional [51, 48, 51, 56, 56] record.midPointType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.optional [50, 53, 48, 48, 55] record.freeText1,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 57] record.stopPx,
   Part.optional [50, 53, 50, 54, 51] record.brokerInternalizationID,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.required [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [51, 49, 54, 50, 53] record.crossMatchInstruction,
   Part.optional [50, 53, 48, 48, 56] record.freeText2,
   Part.optional [50, 53, 49, 48, 55] record.freeText4]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [51, 56, 54] :: NoTradingSessions.members, [[50, 49, 49]], [[56, 51, 54]], [49, 54, 50, 52] :: NoMatchInst.members, [[49, 49, 51, 56]], [[49, 48, 56, 52]], [[49, 48, 56, 53]], [[49, 48, 56, 54]], [50, 53, 57, 51] :: NoOrderAttributes.members, [49, 56, 54, 56] :: NoValueChecks.members, [[49, 49]], [[49, 53]], [[49, 56]], [[51, 56]], [[49, 49, 48]], [[52, 48]], [[51, 48, 51, 56, 56]], [[52, 49]], [[52, 52]], [[53, 52]], [[50, 53, 48, 48, 55]], [[53, 57]], [[57, 57]], [[50, 53, 50, 54, 51]], [[52, 51, 50]], [[49, 55, 50, 52]], [[49, 56, 49, 53]], [[51, 49, 54, 50, 53]], [[50, 53, 48, 48, 56]], [[50, 53, 49, 48, 55]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let pegOffsetType ← readOptional [56, 51, 54] tokens
  let noMatchInst ← readGroup [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.decode tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMethod ← readOptional [49, 48, 56, 52] tokens
  let displayLowQty ← readOptional [49, 48, 56, 53] tokens
  let displayHighQty ← readOptional [49, 48, 56, 54] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let noValueChecks ← readGroup [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.decode tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let ordType ← readRequired [52, 48] tokens
  let midPointType ← readOptional [51, 48, 51, 56, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let freeText1 ← readOptional [50, 53, 48, 48, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let brokerInternalizationID ← readOptional [50, 53, 50, 54, 51] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let tradingCapacity ← readRequired [49, 56, 49, 53] tokens
  let crossMatchInstruction ← readOptional [51, 49, 54, 50, 53] tokens
  let freeText2 ← readOptional [50, 53, 48, 48, 56] tokens
  let freeText4 ← readOptional [50, 53, 49, 48, 55] tokens
  pure { noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noTradingSessions, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderAttributes, noValueChecks, clOrdID, currency, execInst, orderQty, minQty, ordType, midPointType, origClOrdID, price, side, freeText1, timeInForce, stopPx, brokerInternalizationID, expireDate, orderOrigination, tradingCapacity, crossMatchInstruction, freeText2, freeText4 }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have pegOffsetType := readOptional_part [56, 51, 54] record.pegOffsetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noMatchInst := readGroup_part [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.encode NoMatchInst.within NoMatchInst.decode NoMatchInst.decode_encode NoMatchInst.led record.noMatchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have displayMethod := readOptional_part [49, 48, 56, 52] record.displayMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have displayLowQty := readOptional_part [49, 48, 56, 53] record.displayLowQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have displayHighQty := readOptional_part [49, 48, 56, 54] record.displayHighQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noValueChecks := readGroup_part [49, 56, 54, 56] [49, 56, 54, 57] NoValueChecks.members NoValueChecks.encode NoValueChecks.within NoValueChecks.decode NoValueChecks.decode_encode NoValueChecks.led record.noValueChecks tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have midPointType := readOptional_part [51, 48, 51, 56, 56] record.midPointType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have freeText1 := readOptional_part [50, 53, 48, 48, 55] record.freeText1 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have brokerInternalizationID := readOptional_part [50, 53, 50, 54, 51] record.brokerInternalizationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have tradingCapacity := readRequired_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have crossMatchInstruction := readOptional_part [51, 49, 54, 50, 53] record.crossMatchInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have freeText2 := readOptional_part [50, 53, 48, 48, 56] record.freeText2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have freeText4 := readOptional_part [50, 53, 49, 48, 55] record.freeText4 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noTradingSessions, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderAttributes, noValueChecks, clOrdID, currency, execInst, orderQty, minQty, ordType, midPointType, origClOrdID, price, side, freeText1, timeInForce, stopPx, brokerInternalizationID, expireDate, orderOrigination, tradingCapacity, crossMatchInstruction, freeText2, freeText4, some_bind] <;> rfl

structure OrderCancelRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  currency : Option (Terminated 1)  -- tag 15
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderOrigination : Option (Terminated 1)  -- tag 1724

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.optional [49, 53] record.currency,
   Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[49, 53]], [[49, 49]], [[51, 55]], [[52, 49]], [[49, 55, 50, 52]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, clOrdID, orderID, origClOrdID, orderOrigination }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, clOrdID, orderID, origClOrdID, orderOrigination, some_bind] <;> rfl

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  currency : Option (Terminated 1)  -- tag 15
  noPartyIDs : List NoPartyIDs  -- tag 453

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 53] record.currency,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[53, 52]], [[51, 56]], [[49, 53]], [52, 53, 51] :: NoPartyIDs.members]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let currency ← readOptional [49, 53] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  pure { symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, side, orderQty, currency, noPartyIDs }

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
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, side, orderQty, currency, noPartyIDs, some_bind] <;> rfl

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
  noRelatedSym : List NoRelatedSym  -- tag 146
  quoteReqID : Terminated 1  -- tag 131
  privateQuote : Option (Terminated 1)  -- tag 1171
  rFQRequesterDisclosureInstruction : Option (Terminated 1)  -- tag 25139
  rFQPublishIndicator : Option (Terminated 1)  -- tag 28761

def QuoteRequest.parts (record : QuoteRequest) : List Part :=
  [Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [49, 49, 55, 49] record.privateQuote,
   Part.optional [50, 53, 49, 51, 57] record.rFQRequesterDisclosureInstruction,
   Part.optional [50, 56, 55, 54, 49] record.rFQPublishIndicator]

def QuoteRequest.tags : List (List (List UInt8)) :=
  [[49, 52, 54] :: NoRelatedSym.members, [[49, 51, 49]], [[49, 49, 55, 49]], [[50, 53, 49, 51, 57]], [[50, 56, 55, 54, 49]]]

theorem QuoteRequest.shape (record : QuoteRequest) : record.parts.map Part.tags = QuoteRequest.tags := rfl

def QuoteRequest.decode (tokens : List Token) : Option QuoteRequest := do
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let privateQuote ← readOptional [49, 49, 55, 49] tokens
  let rFQRequesterDisclosureInstruction ← readOptional [50, 53, 49, 51, 57] tokens
  let rFQPublishIndicator ← readOptional [50, 56, 55, 54, 49] tokens
  pure { noRelatedSym, quoteReqID, privateQuote, rFQRequesterDisclosureInstruction, rFQPublishIndicator }

theorem QuoteRequest.decode_agrees (record : QuoteRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteRequest.decode tokens = some record := by
  have distinct : QuoteRequest.tags.flatten.Nodup := by decide +kernel
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have privateQuote := readOptional_part [49, 49, 55, 49] record.privateQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rFQRequesterDisclosureInstruction := readOptional_part [50, 53, 49, 51, 57] record.rFQRequesterDisclosureInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rFQPublishIndicator := readOptional_part [50, 56, 55, 54, 49] record.rFQPublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [QuoteRequest.decode, noRelatedSym, quoteReqID, privateQuote, rFQRequesterDisclosureInstruction, rFQPublishIndicator, some_bind] <;> rfl

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  returnCode : Option (Terminated 1)  -- tag 25023

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [50, 53, 48, 50, 51] record.returnCode]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[50, 53, 48, 50, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let returnCode ← readOptional [50, 53, 48, 50, 51] tokens
  pure { refSeqNum, text, refTagID, refMsgType, sessionRejectReason, returnCode }

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
  have returnCode := readOptional_part [50, 53, 48, 50, 51] record.returnCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, returnCode, some_bind] <;> rfl

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

structure NoEvents where
  eventType : Terminated 1  -- tag 865
  eventDate : Option (Terminated 1)  -- tag 866
  eventPx : Option (Terminated 1)  -- tag 867

def NoEvents.parts (record : NoEvents) : List Part :=
  [Part.required [56, 54, 53] record.eventType,
   Part.optional [56, 54, 54] record.eventDate,
   Part.optional [56, 54, 55] record.eventPx]

def NoEvents.tags : List (List (List UInt8)) :=
  [[[56, 54, 53]], [[56, 54, 54]], [[56, 54, 55]]]

theorem NoEvents.shape (record : NoEvents) : record.parts.map Part.tags = NoEvents.tags := rfl

def NoEvents.decode (tokens : List Token) : Option NoEvents := do
  let eventType ← readRequired [56, 54, 53] tokens
  let eventDate ← readOptional [56, 54, 54] tokens
  let eventPx ← readOptional [56, 54, 55] tokens
  pure { eventType, eventDate, eventPx }

theorem NoEvents.decode_agrees (record : NoEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEvents.decode tokens = some record := by
  have distinct : NoEvents.tags.flatten.Nodup := by decide +kernel
  have eventType := readRequired_part [56, 54, 53] record.eventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventDate := readOptional_part [56, 54, 54] record.eventDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have eventPx := readOptional_part [56, 54, 55] record.eventPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoEvents.decode, eventType, eventDate, eventPx, some_bind] <;> rfl

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

structure SecurityStatusDefinitionRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  noEvents : List NoEvents  -- tag 864
  currency : Option (Terminated 1)  -- tag 15
  uTransactTime : Option (Terminated 1)  -- tag 30060
  securityReqID : Terminated 1  -- tag 320
  securityStatusIndicator : Option (Terminated 1)  -- tag 31965
  soldOutIndicator : Option (Terminated 1)  -- tag 25155

def SecurityStatusDefinitionRequest.parts (record : SecurityStatusDefinitionRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.optional [49, 53] record.currency,
   Part.optional [51, 48, 48, 54, 48] record.uTransactTime,
   Part.required [51, 50, 48] record.securityReqID,
   Part.optional [51, 49, 57, 54, 53] record.securityStatusIndicator,
   Part.optional [50, 53, 49, 53, 53] record.soldOutIndicator]

def SecurityStatusDefinitionRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [56, 54, 52] :: NoEvents.members, [[49, 53]], [[51, 48, 48, 54, 48]], [[51, 50, 48]], [[51, 49, 57, 54, 53]], [[50, 53, 49, 53, 53]]]

theorem SecurityStatusDefinitionRequest.shape (record : SecurityStatusDefinitionRequest) : record.parts.map Part.tags = SecurityStatusDefinitionRequest.tags := rfl

def SecurityStatusDefinitionRequest.decode (tokens : List Token) : Option SecurityStatusDefinitionRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let currency ← readOptional [49, 53] tokens
  let uTransactTime ← readOptional [51, 48, 48, 54, 48] tokens
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityStatusIndicator ← readOptional [51, 49, 57, 54, 53] tokens
  let soldOutIndicator ← readOptional [50, 53, 49, 53, 53] tokens
  pure { noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noEvents, currency, uTransactTime, securityReqID, securityStatusIndicator, soldOutIndicator }

theorem SecurityStatusDefinitionRequest.decode_agrees (record : SecurityStatusDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityStatusDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityStatusDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityStatusDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have uTransactTime := readOptional_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityStatusIndicator := readOptional_part [51, 49, 57, 54, 53] record.securityStatusIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have soldOutIndicator := readOptional_part [50, 53, 49, 53, 53] record.soldOutIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [SecurityStatusDefinitionRequest.decode, noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noEvents, currency, uTransactTime, securityReqID, securityStatusIndicator, soldOutIndicator, some_bind] <;> rfl

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

structure NoTargetPartyIDs where
  targetPartyID : Terminated 1  -- tag 1462
  targetPartyIDSource : Terminated 1  -- tag 1463
  targetPartyRole : Terminated 1  -- tag 1464

def NoTargetPartyIDs.parts (record : NoTargetPartyIDs) : List Part :=
  [Part.required [49, 52, 54, 50] record.targetPartyID,
   Part.required [49, 52, 54, 51] record.targetPartyIDSource,
   Part.required [49, 52, 54, 52] record.targetPartyRole]

def NoTargetPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 52, 54, 50]], [[49, 52, 54, 51]], [[49, 52, 54, 52]]]

theorem NoTargetPartyIDs.shape (record : NoTargetPartyIDs) : record.parts.map Part.tags = NoTargetPartyIDs.tags := rfl

def NoTargetPartyIDs.decode (tokens : List Token) : Option NoTargetPartyIDs := do
  let targetPartyID ← readRequired [49, 52, 54, 50] tokens
  let targetPartyIDSource ← readRequired [49, 52, 54, 51] tokens
  let targetPartyRole ← readRequired [49, 52, 54, 52] tokens
  pure { targetPartyID, targetPartyIDSource, targetPartyRole }

theorem NoTargetPartyIDs.decode_agrees (record : NoTargetPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTargetPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTargetPartyIDs.decode tokens = some record := by
  have distinct : NoTargetPartyIDs.tags.flatten.Nodup := by decide +kernel
  have targetPartyID := readRequired_part [49, 52, 54, 50] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetPartyIDSource := readRequired_part [49, 52, 54, 51] record.targetPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetPartyRole := readRequired_part [49, 52, 54, 52] record.targetPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoTargetPartyIDs.decode, targetPartyID, targetPartyIDSource, targetPartyRole, some_bind] <;> rfl

def NoTargetPartyIDs.members : List (List UInt8) := NoTargetPartyIDs.tags.flatten

def NoTargetPartyIDs.encode (entry : NoTargetPartyIDs) : List Token := encodeParts entry.parts

theorem NoTargetPartyIDs.decode_encode (entry : NoTargetPartyIDs) : NoTargetPartyIDs.decode entry.encode = some entry :=
  NoTargetPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTargetPartyIDs.within (entry : NoTargetPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoTargetPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTargetPartyIDs.shape] at this

theorem NoTargetPartyIDs.led (entry : NoTargetPartyIDs) : Lead [49, 52, 54, 50] entry.encode :=
  lead_parts [49, 52, 54, 50] entry.targetPartyID _ NoTargetPartyIDs.tags.tail rfl (by decide +kernel)

structure TradingActionRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  noTargetPartyIDs : List NoTargetPartyIDs  -- tag 1461
  tradingActionRequestID : Terminated 1  -- tag 32328
  riskLimitPlatform : Terminated 1  -- tag 1533
  orderDeletionInstruction : Option (Terminated 1)  -- tag 25272
  partyActionType : Terminated 1  -- tag 2329

def TradingActionRequest.parts (record : TradingActionRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within record.noTargetPartyIDs,
   Part.required [51, 50, 51, 50, 56] record.tradingActionRequestID,
   Part.required [49, 53, 51, 51] record.riskLimitPlatform,
   Part.optional [50, 53, 50, 55, 50] record.orderDeletionInstruction,
   Part.required [50, 51, 50, 57] record.partyActionType]

def TradingActionRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [49, 52, 54, 49] :: NoTargetPartyIDs.members, [[51, 50, 51, 50, 56]], [[49, 53, 51, 51]], [[50, 53, 50, 55, 50]], [[50, 51, 50, 57]]]

theorem TradingActionRequest.shape (record : TradingActionRequest) : record.parts.map Part.tags = TradingActionRequest.tags := rfl

def TradingActionRequest.decode (tokens : List Token) : Option TradingActionRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noTargetPartyIDs ← readGroup [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.decode tokens
  let tradingActionRequestID ← readRequired [51, 50, 51, 50, 56] tokens
  let riskLimitPlatform ← readRequired [49, 53, 51, 51] tokens
  let orderDeletionInstruction ← readOptional [50, 53, 50, 55, 50] tokens
  let partyActionType ← readRequired [50, 51, 50, 57] tokens
  pure { noPartyIDs, noTargetPartyIDs, tradingActionRequestID, riskLimitPlatform, orderDeletionInstruction, partyActionType }

theorem TradingActionRequest.decode_agrees (record : TradingActionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingActionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingActionRequest.decode tokens = some record := by
  have distinct : TradingActionRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noTargetPartyIDs := readGroup_part [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within NoTargetPartyIDs.decode NoTargetPartyIDs.decode_encode NoTargetPartyIDs.led record.noTargetPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingActionRequestID := readRequired_part [51, 50, 51, 50, 56] record.tradingActionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have riskLimitPlatform := readRequired_part [49, 53, 51, 51] record.riskLimitPlatform tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderDeletionInstruction := readOptional_part [50, 53, 50, 55, 50] record.orderDeletionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyActionType := readRequired_part [50, 51, 50, 57] record.partyActionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [TradingActionRequest.decode, noPartyIDs, noTargetPartyIDs, tradingActionRequestID, riskLimitPlatform, orderDeletionInstruction, partyActionType, some_bind] <;> rfl

structure UserOrderMassActionRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  noTargetPartyIDs : List NoTargetPartyIDs  -- tag 1461
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  clOrdID : Terminated 1  -- tag 11
  massActionScope : Terminated 1  -- tag 1374
  currency : Option (Terminated 1)  -- tag 15
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  orderOrigination : Option (Terminated 1)  -- tag 1724

def UserOrderMassActionRequest.parts (record : UserOrderMassActionRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 52, 54, 49] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within record.noTargetPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 51, 55, 52] record.massActionScope,
   Part.optional [49, 53] record.currency,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.optional [49, 55, 50, 52] record.orderOrigination]

def UserOrderMassActionRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [49, 52, 54, 49] :: NoTargetPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[49, 49]], [[49, 51, 55, 52]], [[49, 53]], [[52, 52]], [[53, 52]], [[49, 55, 50, 52]]]

theorem UserOrderMassActionRequest.shape (record : UserOrderMassActionRequest) : record.parts.map Part.tags = UserOrderMassActionRequest.tags := rfl

def UserOrderMassActionRequest.decode (tokens : List Token) : Option UserOrderMassActionRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noTargetPartyIDs ← readGroup [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let massActionScope ← readRequired [49, 51, 55, 52] tokens
  let currency ← readOptional [49, 53] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  pure { noPartyIDs, noTargetPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, clOrdID, massActionScope, currency, price, side, orderOrigination }

theorem UserOrderMassActionRequest.decode_agrees (record : UserOrderMassActionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserOrderMassActionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserOrderMassActionRequest.decode tokens = some record := by
  have distinct : UserOrderMassActionRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noTargetPartyIDs := readGroup_part [49, 52, 54, 49] [49, 52, 54, 50] NoTargetPartyIDs.members NoTargetPartyIDs.encode NoTargetPartyIDs.within NoTargetPartyIDs.decode NoTargetPartyIDs.decode_encode NoTargetPartyIDs.led record.noTargetPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have massActionScope := readRequired_part [49, 51, 55, 52] record.massActionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [UserOrderMassActionRequest.decode, noPartyIDs, noTargetPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, clOrdID, massActionScope, currency, price, side, orderOrigination, some_bind] <;> rfl

structure UserPartyRiskLimitsRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  marketSegmentID : Terminated 1  -- tag 1300
  riskLimitPlatform : Terminated 1  -- tag 1533
  riskLimitRequestID : Terminated 1  -- tag 1666
  riskLimitGroup : Option (Terminated 1)  -- tag 28775

def UserPartyRiskLimitsRequest.parts (record : UserPartyRiskLimitsRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [49, 51, 48, 48] record.marketSegmentID,
   Part.required [49, 53, 51, 51] record.riskLimitPlatform,
   Part.required [49, 54, 54, 54] record.riskLimitRequestID,
   Part.optional [50, 56, 55, 55, 53] record.riskLimitGroup]

def UserPartyRiskLimitsRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49, 51, 48, 48]], [[49, 53, 51, 51]], [[49, 54, 54, 54]], [[50, 56, 55, 55, 53]]]

theorem UserPartyRiskLimitsRequest.shape (record : UserPartyRiskLimitsRequest) : record.parts.map Part.tags = UserPartyRiskLimitsRequest.tags := rfl

def UserPartyRiskLimitsRequest.decode (tokens : List Token) : Option UserPartyRiskLimitsRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let marketSegmentID ← readRequired [49, 51, 48, 48] tokens
  let riskLimitPlatform ← readRequired [49, 53, 51, 51] tokens
  let riskLimitRequestID ← readRequired [49, 54, 54, 54] tokens
  let riskLimitGroup ← readOptional [50, 56, 55, 55, 53] tokens
  pure { noPartyIDs, marketSegmentID, riskLimitPlatform, riskLimitRequestID, riskLimitGroup }

theorem UserPartyRiskLimitsRequest.decode_agrees (record : UserPartyRiskLimitsRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserPartyRiskLimitsRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserPartyRiskLimitsRequest.decode tokens = some record := by
  have distinct : UserPartyRiskLimitsRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketSegmentID := readRequired_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have riskLimitPlatform := readRequired_part [49, 53, 51, 51] record.riskLimitPlatform tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have riskLimitRequestID := readRequired_part [49, 54, 54, 54] record.riskLimitRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have riskLimitGroup := readOptional_part [50, 56, 55, 55, 53] record.riskLimitGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [UserPartyRiskLimitsRequest.decode, noPartyIDs, marketSegmentID, riskLimitPlatform, riskLimitRequestID, riskLimitGroup, some_bind] <;> rfl

structure UserRequest where
  username : Terminated 1  -- tag 553
  password : Option (Terminated 1)  -- tag 554
  userRequestID : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924

def UserRequest.parts (record : UserRequest) : List Part :=
  [Part.required [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password,
   Part.required [57, 50, 51] record.userRequestID,
   Part.required [57, 50, 52] record.userRequestType]

def UserRequest.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]], [[53, 53, 52]], [[57, 50, 51]], [[57, 50, 52]]]

theorem UserRequest.shape (record : UserRequest) : record.parts.map Part.tags = UserRequest.tags := rfl

def UserRequest.decode (tokens : List Token) : Option UserRequest := do
  let username ← readRequired [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  pure { username, password, userRequestID, userRequestType }

theorem UserRequest.decode_agrees (record : UserRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserRequest.decode tokens = some record := by
  have distinct : UserRequest.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [UserRequest.decode, username, password, userRequestID, userRequestType, some_bind] <;> rfl

inductive Message where
  | crossRequest (header : Header) (r0 : CrossRequest)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | quoteRequest (header : Header) (r0 : QuoteRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityStatusDefinitionRequest (header : Header) (r0 : SecurityStatusDefinitionRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradingActionRequest (header : Header) (r0 : TradingActionRequest)
  | userOrderMassActionRequest (header : Header) (r0 : UserOrderMassActionRequest)
  | userPartyRiskLimitsRequest (header : Header) (r0 : UserPartyRiskLimitsRequest)
  | userRequest (header : Header) (r0 : UserRequest)

def Message.tokens : Message → List Token
  | .crossRequest header r0 => ⟨[51, 53], ⟨[85, 68, 83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteRequest header r0 => ⟨[51, 53], ⟨[82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityStatusDefinitionRequest header r0 => ⟨[51, 53], ⟨[85, 50, 55], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingActionRequest header r0 => ⟨[51, 53], ⟨[85, 51, 52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userOrderMassActionRequest header r0 => ⟨[51, 53], ⟨[85, 67, 65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userPartyRiskLimitsRequest header r0 => ⟨[51, 53], ⟨[85, 67, 76], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userRequest header r0 => ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [85, 68, 83] then
        if known (Header.tags ++ CrossRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CrossRequest.decode rest
          pure (.crossRequest header r0)
        else none
      else if token.value.val = [48] then
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
      else if token.value.val = [82] then
        if known (Header.tags ++ QuoteRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteRequest.decode rest
          pure (.quoteRequest header r0)
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
      else if token.value.val = [85, 50, 55] then
        if known (Header.tags ++ SecurityStatusDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityStatusDefinitionRequest.decode rest
          pure (.securityStatusDefinitionRequest header r0)
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
      else if token.value.val = [85, 51, 52] then
        if known (Header.tags ++ TradingActionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingActionRequest.decode rest
          pure (.tradingActionRequest header r0)
        else none
      else if token.value.val = [85, 67, 65] then
        if known (Header.tags ++ UserOrderMassActionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserOrderMassActionRequest.decode rest
          pure (.userOrderMassActionRequest header r0)
        else none
      else if token.value.val = [85, 67, 76] then
        if known (Header.tags ++ UserPartyRiskLimitsRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserPartyRiskLimitsRequest.decode rest
          pure (.userPartyRiskLimitsRequest header r0)
        else none
      else if token.value.val = [66, 69] then
        if known (Header.tags ++ UserRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserRequest.decode rest
          pure (.userRequest header r0)
        else none
      else none
    else none

theorem Message.decode_crossRequest (header : Header) (r0 : CrossRequest) :
    Message.decode (Message.tokens (.crossRequest header r0)) = some (.crossRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CrossRequest.tags) rfl rfl (by decide +kernel))
  have c1 := CrossRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CrossRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CrossRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

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

theorem Message.decode_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decode (Message.tokens (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags) rfl
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

theorem Message.decode_securityStatusDefinitionRequest (header : Header) (r0 : SecurityStatusDefinitionRequest) :
    Message.decode (Message.tokens (.securityStatusDefinitionRequest header r0)) = some (.securityStatusDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityStatusDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityStatusDefinitionRequest.tags) rfl
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

theorem Message.decode_tradingActionRequest (header : Header) (r0 : TradingActionRequest) :
    Message.decode (Message.tokens (.tradingActionRequest header r0)) = some (.tradingActionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingActionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradingActionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingActionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingActionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userOrderMassActionRequest (header : Header) (r0 : UserOrderMassActionRequest) :
    Message.decode (Message.tokens (.userOrderMassActionRequest header r0)) = some (.userOrderMassActionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserOrderMassActionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserOrderMassActionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserOrderMassActionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserOrderMassActionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userPartyRiskLimitsRequest (header : Header) (r0 : UserPartyRiskLimitsRequest) :
    Message.decode (Message.tokens (.userPartyRiskLimitsRequest header r0)) = some (.userPartyRiskLimitsRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserPartyRiskLimitsRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserPartyRiskLimitsRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userRequest (header : Header) (r0 : UserRequest) :
    Message.decode (Message.tokens (.userRequest header r0)) = some (.userRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | crossRequest header r0 => exact Message.decode_crossRequest header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | quoteRequest header r0 => exact Message.decode_quoteRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityStatusDefinitionRequest header r0 => exact Message.decode_securityStatusDefinitionRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradingActionRequest header r0 => exact Message.decode_tradingActionRequest header r0
  | userOrderMassActionRequest header r0 => exact Message.decode_userOrderMassActionRequest header r0
  | userPartyRiskLimitsRequest header r0 => exact Message.decode_userPartyRiskLimitsRequest header r0
  | userRequest header r0 => exact Message.decode_userRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_crossRequest (header : Header) (r0 : CrossRequest) :
    Message.decodeBytes (Message.encode (.crossRequest header r0)) = some (.crossRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68, 83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CrossRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_crossRequest header r0

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

theorem Message.decodeBytes_quoteRequest (header : Header) (r0 : QuoteRequest) :
    Message.decodeBytes (Message.encode (.quoteRequest header r0)) = some (.quoteRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteRequest header r0

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

theorem Message.decodeBytes_securityStatusDefinitionRequest (header : Header) (r0 : SecurityStatusDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityStatusDefinitionRequest header r0)) = some (.securityStatusDefinitionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 50, 55], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityStatusDefinitionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityStatusDefinitionRequest header r0

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

theorem Message.decodeBytes_tradingActionRequest (header : Header) (r0 : TradingActionRequest) :
    Message.decodeBytes (Message.encode (.tradingActionRequest header r0)) = some (.tradingActionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 51, 52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradingActionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingActionRequest header r0

theorem Message.decodeBytes_userOrderMassActionRequest (header : Header) (r0 : UserOrderMassActionRequest) :
    Message.decodeBytes (Message.encode (.userOrderMassActionRequest header r0)) = some (.userOrderMassActionRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 67, 65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserOrderMassActionRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userOrderMassActionRequest header r0

theorem Message.decodeBytes_userPartyRiskLimitsRequest (header : Header) (r0 : UserPartyRiskLimitsRequest) :
    Message.decodeBytes (Message.encode (.userPartyRiskLimitsRequest header r0)) = some (.userPartyRiskLimitsRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 67, 76], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserPartyRiskLimitsRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userPartyRiskLimitsRequest header r0

theorem Message.decodeBytes_userRequest (header : Header) (r0 : UserRequest) :
    Message.decodeBytes (Message.encode (.userRequest header r0)) = some (.userRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[66, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | crossRequest header r0 => exact Message.decodeBytes_crossRequest header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | quoteRequest header r0 => exact Message.decodeBytes_quoteRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityStatusDefinitionRequest header r0 => exact Message.decodeBytes_securityStatusDefinitionRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradingActionRequest header r0 => exact Message.decodeBytes_tradingActionRequest header r0
  | userOrderMassActionRequest header r0 => exact Message.decodeBytes_userOrderMassActionRequest header r0
  | userPartyRiskLimitsRequest header r0 => exact Message.decodeBytes_userPartyRiskLimitsRequest header r0
  | userRequest header r0 => exact Message.decodeBytes_userRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.EurexT7CashorderentryFixV150Client
