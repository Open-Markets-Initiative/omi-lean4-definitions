import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Order Entry v13.4, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqPhlxoptionsOrderentryFixV134Client

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  senderSubID : Option (Terminated 1)  -- tag 50
  possDupFlag : Option (Terminated 1)  -- tag 43
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[53, 50]], [[52, 57]], [[53, 54]], [[53, 48]], [[52, 51]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, sendingTime, senderCompID, targetCompID, senderSubID, possDupFlag, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, sendingTime, senderCompID, targetCompID, senderSubID, possDupFlag, origSendingTime, some_bind] <;> rfl

structure NoExecs where
  execID : Terminated 1  -- tag 17

def NoExecs.parts (record : NoExecs) : List Part :=
  [Part.required [49, 55] record.execID]

def NoExecs.tags : List (List (List UInt8)) :=
  [[[49, 55]]]

theorem NoExecs.shape (record : NoExecs) : record.parts.map Part.tags = NoExecs.tags := rfl

def NoExecs.decode (tokens : List Token) : Option NoExecs := do
  let execID ← readRequired [49, 55] tokens
  pure { execID }

theorem NoExecs.decode_agrees (record : NoExecs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoExecs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoExecs.decode tokens = some record := by
  have distinct : NoExecs.tags.flatten.Nodup := by decide +kernel
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoExecs.decode, execID, some_bind] <;> rfl

def NoExecs.members : List (List UInt8) := NoExecs.tags.flatten

def NoExecs.encode (entry : NoExecs) : List Token := encodeParts entry.parts

theorem NoExecs.decode_encode (entry : NoExecs) : NoExecs.decode entry.encode = some entry :=
  NoExecs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoExecs.within (entry : NoExecs) : ∀ token ∈ entry.encode, token.tag ∈ NoExecs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoExecs.shape] at this

theorem NoExecs.led (entry : NoExecs) : Lead [49, 55] entry.encode :=
  lead_parts [49, 55] entry.execID _ NoExecs.tags.tail rfl (by decide +kernel)

structure NoAllocs where
  allocShares : Terminated 1  -- tag 80
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  execBroker : Terminated 1  -- tag 76
  openClose : Option (Terminated 1)  -- tag 77
  customerOrFirm : Option (Terminated 1)  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  rule80A : Option (Terminated 1)  -- tag 47

def NoAllocs.parts (record : NoAllocs) : List Part :=
  [Part.required [56, 48] record.allocShares,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.required [55, 54] record.execBroker,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.optional [52, 55] record.rule80A]

def NoAllocs.tags : List (List (List UInt8)) :=
  [[[56, 48]], [[49]], [[53, 56]], [[55, 54]], [[55, 55]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[57, 48, 55, 54]], [[52, 55]]]

theorem NoAllocs.shape (record : NoAllocs) : record.parts.map Part.tags = NoAllocs.tags := rfl

def NoAllocs.decode (tokens : List Token) : Option NoAllocs := do
  let allocShares ← readRequired [56, 48] tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readRequired [55, 54] tokens
  let openClose ← readOptional [55, 55] tokens
  let customerOrFirm ← readOptional [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let rule80A ← readOptional [52, 55] tokens
  pure { allocShares, account, text, execBroker, openClose, customerOrFirm, clearingFirm, clearingAccount, stockLegGiveUp, rule80A }

theorem NoAllocs.decode_agrees (record : NoAllocs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAllocs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAllocs.decode tokens = some record := by
  have distinct : NoAllocs.tags.flatten.Nodup := by decide +kernel
  have allocShares := readRequired_part [56, 48] record.allocShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execBroker := readRequired_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have customerOrFirm := readOptional_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoAllocs.decode, allocShares, account, text, execBroker, openClose, customerOrFirm, clearingFirm, clearingAccount, stockLegGiveUp, rule80A, some_bind] <;> rfl

def NoAllocs.members : List (List UInt8) := NoAllocs.tags.flatten

def NoAllocs.encode (entry : NoAllocs) : List Token := encodeParts entry.parts

theorem NoAllocs.decode_encode (entry : NoAllocs) : NoAllocs.decode entry.encode = some entry :=
  NoAllocs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAllocs.within (entry : NoAllocs) : ∀ token ∈ entry.encode, token.tag ∈ NoAllocs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAllocs.shape] at this

theorem NoAllocs.led (entry : NoAllocs) : Lead [56, 48] entry.encode :=
  lead_parts [56, 48] entry.allocShares _ NoAllocs.tags.tail rfl (by decide +kernel)

structure Allocation where
  securityID : Option (Terminated 1)  -- tag 48
  shares : Terminated 1  -- tag 53
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60
  allocID : Terminated 1  -- tag 70
  allocTransType : Terminated 1  -- tag 71
  clOrdID : Terminated 1  -- tag 11
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDate : Option (Terminated 1)  -- tag 541
  noExecs : List NoExecs  -- tag 124
  noAllocs : List NoAllocs  -- tag 78

def Allocation.parts (record : Allocation) : List Part :=
  [Part.optional [52, 56] record.securityID,
   Part.required [53, 51] record.shares,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 48] record.allocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [49, 49] record.clOrdID,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.group [49, 50, 52] NoExecs.members NoExecs.encode NoExecs.within record.noExecs,
   Part.group [55, 56] NoAllocs.members NoAllocs.encode NoAllocs.within record.noAllocs]

def Allocation.tags : List (List (List UInt8)) :=
  [[[52, 56]], [[53, 51]], [[53, 52]], [[53, 53]], [[54, 48]], [[55, 48]], [[55, 49]], [[49, 49]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52, 49]], [49, 50, 52] :: NoExecs.members, [55, 56] :: NoAllocs.members]

theorem Allocation.shape (record : Allocation) : record.parts.map Part.tags = Allocation.tags := rfl

def Allocation.decode (tokens : List Token) : Option Allocation := do
  let securityID ← readOptional [52, 56] tokens
  let shares ← readRequired [53, 51] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let allocID ← readRequired [55, 48] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let noExecs ← readGroup [49, 50, 52] [49, 55] NoExecs.members NoExecs.decode tokens
  let noAllocs ← readGroup [55, 56] [56, 48] NoAllocs.members NoAllocs.decode tokens
  pure { securityID, shares, side, symbol, transactTime, allocID, allocTransType, clOrdID, putOrCall, strikePrice, maturityDate, noExecs, noAllocs }

theorem Allocation.decode_agrees (record : Allocation) (tokens : List Token)
    (agrees : ∀ tags ∈ Allocation.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Allocation.decode tokens = some record := by
  have distinct : Allocation.tags.flatten.Nodup := by decide +kernel
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have shares := readRequired_part [53, 51] record.shares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noExecs := readGroup_part [49, 50, 52] [49, 55] NoExecs.members NoExecs.encode NoExecs.within NoExecs.decode NoExecs.decode_encode NoExecs.led record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noAllocs := readGroup_part [55, 56] [56, 48] NoAllocs.members NoAllocs.encode NoAllocs.within NoAllocs.decode NoAllocs.decode_encode NoAllocs.led record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [Allocation.decode, securityID, shares, side, symbol, transactTime, allocID, allocTransType, clOrdID, putOrCall, strikePrice, maturityDate, noExecs, noAllocs, some_bind] <;> rfl

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

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  pure { encryptMethod, heartBtInt }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, some_bind] <;> rfl

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

structure NoPartyDetails where
  partyDetailID : Terminated 1  -- tag 1691
  partyDetailRole : Terminated 1  -- tag 1693

def NoPartyDetails.parts (record : NoPartyDetails) : List Part :=
  [Part.required [49, 54, 57, 49] record.partyDetailID,
   Part.required [49, 54, 57, 51] record.partyDetailRole]

def NoPartyDetails.tags : List (List (List UInt8)) :=
  [[[49, 54, 57, 49]], [[49, 54, 57, 51]]]

theorem NoPartyDetails.shape (record : NoPartyDetails) : record.parts.map Part.tags = NoPartyDetails.tags := rfl

def NoPartyDetails.decode (tokens : List Token) : Option NoPartyDetails := do
  let partyDetailID ← readRequired [49, 54, 57, 49] tokens
  let partyDetailRole ← readRequired [49, 54, 57, 51] tokens
  pure { partyDetailID, partyDetailRole }

theorem NoPartyDetails.decode_agrees (record : NoPartyDetails) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyDetails.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyDetails.decode tokens = some record := by
  have distinct : NoPartyDetails.tags.flatten.Nodup := by decide +kernel
  have partyDetailID := readRequired_part [49, 54, 57, 49] record.partyDetailID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyDetailRole := readRequired_part [49, 54, 57, 51] record.partyDetailRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoPartyDetails.decode, partyDetailID, partyDetailRole, some_bind] <;> rfl

def NoPartyDetails.members : List (List UInt8) := NoPartyDetails.tags.flatten

def NoPartyDetails.encode (entry : NoPartyDetails) : List Token := encodeParts entry.parts

theorem NoPartyDetails.decode_encode (entry : NoPartyDetails) : NoPartyDetails.decode entry.encode = some entry :=
  NoPartyDetails.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyDetails.within (entry : NoPartyDetails) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyDetails.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyDetails.shape] at this

theorem NoPartyDetails.led (entry : NoPartyDetails) : Lead [49, 54, 57, 49] entry.encode :=
  lead_parts [49, 54, 57, 49] entry.partyDetailID _ NoPartyDetails.tags.tail rfl (by decide +kernel)

structure NoPartyEntitlements where
  listUpdateAction : Terminated 1  -- tag 1324
  noPartyDetails : List NoPartyDetails  -- tag 1671
  entitlementStatus : Option (Terminated 1)  -- tag 1883

def NoPartyEntitlements.parts (record : NoPartyEntitlements) : List Part :=
  [Part.required [49, 51, 50, 52] record.listUpdateAction,
   Part.group [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within record.noPartyDetails,
   Part.optional [49, 56, 56, 51] record.entitlementStatus]

def NoPartyEntitlements.tags : List (List (List UInt8)) :=
  [[[49, 51, 50, 52]], [49, 54, 55, 49] :: NoPartyDetails.members, [[49, 56, 56, 51]]]

theorem NoPartyEntitlements.shape (record : NoPartyEntitlements) : record.parts.map Part.tags = NoPartyEntitlements.tags := rfl

def NoPartyEntitlements.decode (tokens : List Token) : Option NoPartyEntitlements := do
  let listUpdateAction ← readRequired [49, 51, 50, 52] tokens
  let noPartyDetails ← readGroup [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.decode tokens
  let entitlementStatus ← readOptional [49, 56, 56, 51] tokens
  pure { listUpdateAction, noPartyDetails, entitlementStatus }

theorem NoPartyEntitlements.decode_agrees (record : NoPartyEntitlements) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyEntitlements.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyEntitlements.decode tokens = some record := by
  have distinct : NoPartyEntitlements.tags.flatten.Nodup := by decide +kernel
  have listUpdateAction := readRequired_part [49, 51, 50, 52] record.listUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyDetails := readGroup_part [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within NoPartyDetails.decode NoPartyDetails.decode_encode NoPartyDetails.led record.noPartyDetails tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have entitlementStatus := readOptional_part [49, 56, 56, 51] record.entitlementStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoPartyEntitlements.decode, listUpdateAction, noPartyDetails, entitlementStatus, some_bind] <;> rfl

def NoPartyEntitlements.members : List (List UInt8) := NoPartyEntitlements.tags.flatten

def NoPartyEntitlements.encode (entry : NoPartyEntitlements) : List Token := encodeParts entry.parts

theorem NoPartyEntitlements.decode_encode (entry : NoPartyEntitlements) : NoPartyEntitlements.decode entry.encode = some entry :=
  NoPartyEntitlements.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyEntitlements.within (entry : NoPartyEntitlements) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyEntitlements.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyEntitlements.shape] at this

theorem NoPartyEntitlements.led (entry : NoPartyEntitlements) : Lead [49, 51, 50, 52] entry.encode :=
  lead_parts [49, 51, 50, 52] entry.listUpdateAction _ NoPartyEntitlements.tags.tail rfl (by decide +kernel)

structure MemberKillSwitch where
  entitlementRequestID : Terminated 1  -- tag 1770
  noPartyEntitlements : List NoPartyEntitlements  -- tag 1772

def MemberKillSwitch.parts (record : MemberKillSwitch) : List Part :=
  [Part.required [49, 55, 55, 48] record.entitlementRequestID,
   Part.group [49, 55, 55, 50] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within record.noPartyEntitlements]

def MemberKillSwitch.tags : List (List (List UInt8)) :=
  [[[49, 55, 55, 48]], [49, 55, 55, 50] :: NoPartyEntitlements.members]

theorem MemberKillSwitch.shape (record : MemberKillSwitch) : record.parts.map Part.tags = MemberKillSwitch.tags := rfl

def MemberKillSwitch.decode (tokens : List Token) : Option MemberKillSwitch := do
  let entitlementRequestID ← readRequired [49, 55, 55, 48] tokens
  let noPartyEntitlements ← readGroup [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.decode tokens
  pure { entitlementRequestID, noPartyEntitlements }

theorem MemberKillSwitch.decode_agrees (record : MemberKillSwitch) (tokens : List Token)
    (agrees : ∀ tags ∈ MemberKillSwitch.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MemberKillSwitch.decode tokens = some record := by
  have distinct : MemberKillSwitch.tags.flatten.Nodup := by decide +kernel
  have entitlementRequestID := readRequired_part [49, 55, 55, 48] record.entitlementRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyEntitlements := readGroup_part [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within NoPartyEntitlements.decode NoPartyEntitlements.decode_encode NoPartyEntitlements.led record.noPartyEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [MemberKillSwitch.decode, entitlementRequestID, noPartyEntitlements, some_bind] <;> rfl

structure NoLegs where
  legRefID : Terminated 1  -- tag 654
  legPositionEffect : Terminated 1  -- tag 564
  legPrice : Option (Terminated 1)  -- tag 566
  legSymbol : Terminated 1  -- tag 600
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Terminated 1  -- tag 611
  legStrikePrice : Terminated 1  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  contraLegPositionEffect : Terminated 1  -- tag 9564
  contraSideShortSell : Terminated 1  -- tag 9624

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 53, 52] record.legRefID,
   Part.required [53, 54, 52] record.legPositionEffect,
   Part.optional [53, 54, 54] record.legPrice,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 56] record.legCFICode,
   Part.required [54, 49, 49] record.legMaturityDate,
   Part.required [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.required [57, 53, 54, 52] record.contraLegPositionEffect,
   Part.required [57, 54, 50, 52] record.contraSideShortSell]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 53, 52]], [[53, 54, 52]], [[53, 54, 54]], [[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[57, 53, 54, 52]], [[57, 54, 50, 52]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legRefID ← readRequired [54, 53, 52] tokens
  let legPositionEffect ← readRequired [53, 54, 52] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readRequired [54, 49, 49] tokens
  let legStrikePrice ← readRequired [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let contraLegPositionEffect ← readRequired [57, 53, 54, 52] tokens
  let contraSideShortSell ← readRequired [57, 54, 50, 52] tokens
  pure { legRefID, legPositionEffect, legPrice, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legPositionEffect := readRequired_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legMaturityDate := readRequired_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legStrikePrice := readRequired_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contraLegPositionEffect := readRequired_part [57, 53, 54, 52] record.contraLegPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have contraSideShortSell := readRequired_part [57, 54, 50, 52] record.contraSideShortSell tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [NoLegs.decode, legRefID, legPositionEffect, legPrice, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell, some_bind] <;> rfl

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

structure MultilegOrderCancelReplace where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  allocAccount : Option (Terminated 1)  -- tag 79
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  noLegs : List NoLegs  -- tag 555

def MultilegOrderCancelReplace.parts (record : MultilegOrderCancelReplace) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [55, 57] record.allocAccount,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def MultilegOrderCancelReplace.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 56]], [[57, 48, 52, 51]], [[57, 48, 52, 52]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 57]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 57, 50]], [53, 53, 53] :: NoLegs.members]

theorem MultilegOrderCancelReplace.shape (record : MultilegOrderCancelReplace) : record.parts.map Part.tags = MultilegOrderCancelReplace.tags := rfl

def MultilegOrderCancelReplace.decode (tokens : List Token) : Option MultilegOrderCancelReplace := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  pure { account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, text, stepUpPriceType, stepUpPrice, timeInForce, transactTime, execBroker, allocAccount, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, priceProtectionScope, noLegs }

theorem MultilegOrderCancelReplace.decode_agrees (record : MultilegOrderCancelReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegOrderCancelReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegOrderCancelReplace.decode tokens = some record := by
  have distinct : MultilegOrderCancelReplace.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [MultilegOrderCancelReplace.decode, account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, text, stepUpPriceType, stepUpPrice, timeInForce, transactTime, execBroker, allocAccount, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, priceProtectionScope, noLegs, some_bind] <;> rfl

structure NoSides where
  clOrdID : Terminated 1  -- tag 11
  side : Option (Terminated 1)  -- tag 54
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Option (Terminated 1)  -- tag 77
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  allocAccount : Option (Terminated 1)  -- tag 79
  rule80A : Option (Terminated 1)  -- tag 47
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.optional [55, 55] record.openClose,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [52, 55] record.rule80A,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp]

def NoSides.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 52]], [[49]], [[53, 56]], [[55, 54]], [[55, 55]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 57]], [[52, 52, 48]], [[55, 57]], [[52, 55]], [[57, 48, 55, 54]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let clOrdID ← readRequired [49, 49] tokens
  let side ← readOptional [53, 52] tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readOptional [55, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  pure { clOrdID, side, account, text, execBroker, openClose, customerOrFirm, securityExchange, clearingFirm, clearingAccount, allocAccount, rule80A, stockLegGiveUp }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [NoSides.decode, clOrdID, side, account, text, execBroker, openClose, customerOrFirm, securityExchange, clearingFirm, clearingAccount, allocAccount, rule80A, stockLegGiveUp, some_bind] <;> rfl

def NoSides.members : List (List UInt8) := NoSides.tags.flatten

def NoSides.encode (entry : NoSides) : List Token := encodeParts entry.parts

theorem NoSides.decode_encode (entry : NoSides) : NoSides.decode entry.encode = some entry :=
  NoSides.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSides.within (entry : NoSides) : ∀ token ∈ entry.encode, token.tag ∈ NoSides.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSides.shape] at this

theorem NoSides.led (entry : NoSides) : Lead [49, 49] entry.encode :=
  lead_parts [49, 49] entry.clOrdID _ NoSides.tags.tail rfl (by decide +kernel)

structure NewOrderCross where
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDate : Terminated 1  -- tag 541
  crossID : Terminated 1  -- tag 548
  auctionType : Terminated 1  -- tag 9373
  auctionDuration : Option (Terminated 1)  -- tag 9379
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  brokerPCT : Option (Terminated 1)  -- tag 9204
  priceDelta : Option (Terminated 1)  -- tag 9811
  noSides : List NoSides  -- tag 552

def NewOrderCross.parts (record : NewOrderCross) : List Part :=
  [Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [53, 52, 56] record.crossID,
   Part.required [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 57] record.auctionDuration,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 50, 48, 52] record.brokerPCT,
   Part.optional [57, 56, 49, 49] record.priceDelta,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides]

def NewOrderCross.tags : List (List (List UInt8)) :=
  [[[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52, 49]], [[53, 52, 56]], [[57, 51, 55, 51]], [[57, 51, 55, 57]], [[57, 48, 52, 51]], [[57, 48, 52, 52]], [[57, 50, 48, 52]], [[57, 56, 49, 49]], [53, 53, 50] :: NoSides.members]

theorem NewOrderCross.shape (record : NewOrderCross) : record.parts.map Part.tags = NewOrderCross.tags := rfl

def NewOrderCross.decode (tokens : List Token) : Option NewOrderCross := do
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let auctionType ← readRequired [57, 51, 55, 51] tokens
  let auctionDuration ← readOptional [57, 51, 55, 57] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let brokerPCT ← readOptional [57, 50, 48, 52] tokens
  let priceDelta ← readOptional [57, 56, 49, 49] tokens
  let noSides ← readGroup [53, 53, 50] [49, 49] NoSides.members NoSides.decode tokens
  pure { execInst, orderQty, ordType, price, symbol, timeInForce, transactTime, putOrCall, strikePrice, maturityDate, crossID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice, brokerPCT, priceDelta, noSides }

theorem NewOrderCross.decode_agrees (record : NewOrderCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCross.decode tokens = some record := by
  have distinct : NewOrderCross.tags.flatten.Nodup := by decide +kernel
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have auctionType := readRequired_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have auctionDuration := readOptional_part [57, 51, 55, 57] record.auctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have brokerPCT := readOptional_part [57, 50, 48, 52] record.brokerPCT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have priceDelta := readOptional_part [57, 56, 49, 49] record.priceDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [49, 49] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [NewOrderCross.decode, execInst, orderQty, ordType, price, symbol, timeInForce, transactTime, putOrCall, strikePrice, maturityDate, crossID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice, brokerPCT, priceDelta, noSides, some_bind] <;> rfl

structure NewOrderCrossMultileg where
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  crossID : Terminated 1  -- tag 548
  auctionType : Terminated 1  -- tag 9373
  auctionDuration : Option (Terminated 1)  -- tag 9379
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  brokerPCT : Option (Terminated 1)  -- tag 9204
  underlyingPx : Option (Terminated 1)  -- tag 810
  underlyingQty : Option (Terminated 1)  -- tag 879
  priceDelta : Option (Terminated 1)  -- tag 9811
  noSides : List NoSides  -- tag 552
  noLegs : List NoLegs  -- tag 555

def NewOrderCrossMultileg.parts (record : NewOrderCrossMultileg) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.required [53, 52, 56] record.crossID,
   Part.required [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 57] record.auctionDuration,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 50, 48, 52] record.brokerPCT,
   Part.optional [56, 49, 48] record.underlyingPx,
   Part.optional [56, 55, 57] record.underlyingQty,
   Part.optional [57, 56, 49, 49] record.priceDelta,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def NewOrderCrossMultileg.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 48]], [[52, 52]], [[53, 57]], [[54, 48]], [[53, 52, 56]], [[57, 51, 55, 51]], [[57, 51, 55, 57]], [[57, 48, 52, 51]], [[57, 48, 52, 52]], [[57, 50, 48, 52]], [[56, 49, 48]], [[56, 55, 57]], [[57, 56, 49, 49]], [53, 53, 50] :: NoSides.members, [53, 53, 53] :: NoLegs.members]

theorem NewOrderCrossMultileg.shape (record : NewOrderCrossMultileg) : record.parts.map Part.tags = NewOrderCrossMultileg.tags := rfl

def NewOrderCrossMultileg.decode (tokens : List Token) : Option NewOrderCrossMultileg := do
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let auctionType ← readRequired [57, 51, 55, 51] tokens
  let auctionDuration ← readOptional [57, 51, 55, 57] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let brokerPCT ← readOptional [57, 50, 48, 52] tokens
  let underlyingPx ← readOptional [56, 49, 48] tokens
  let underlyingQty ← readOptional [56, 55, 57] tokens
  let priceDelta ← readOptional [57, 56, 49, 49] tokens
  let noSides ← readGroup [53, 53, 50] [49, 49] NoSides.members NoSides.decode tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  pure { orderQty, ordType, price, timeInForce, transactTime, crossID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice, brokerPCT, underlyingPx, underlyingQty, priceDelta, noSides, noLegs }

theorem NewOrderCrossMultileg.decode_agrees (record : NewOrderCrossMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCrossMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCrossMultileg.decode tokens = some record := by
  have distinct : NewOrderCrossMultileg.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have auctionType := readRequired_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have auctionDuration := readOptional_part [57, 51, 55, 57] record.auctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have brokerPCT := readOptional_part [57, 50, 48, 52] record.brokerPCT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have underlyingPx := readOptional_part [56, 49, 48] record.underlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have underlyingQty := readOptional_part [56, 55, 57] record.underlyingQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have priceDelta := readOptional_part [57, 56, 49, 49] record.priceDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [49, 49] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NewOrderCrossMultileg.decode, orderQty, ordType, price, timeInForce, transactTime, crossID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice, brokerPCT, underlyingPx, underlyingQty, priceDelta, noSides, noLegs, some_bind] <;> rfl

structure NewOrderMultileg where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  rule80A : Option (Terminated 1)  -- tag 47
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  allocAccount : Option (Terminated 1)  -- tag 79
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  specialOrdType : Option (Terminated 1)  -- tag 9202
  exposureFlag : Option (Terminated 1)  -- tag 9203
  auctionID : Option (Terminated 1)  -- tag 9370
  auctionType : Option (Terminated 1)  -- tag 9373
  auctionDuration : Option (Terminated 1)  -- tag 9379
  noLegs : List NoLegs  -- tag 555

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.rule80A,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [55, 57] record.allocAccount,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 57] record.auctionDuration,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 55]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 57]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 57, 50]], [[57, 48, 55, 54]], [[57, 50, 48, 50]], [[57, 50, 48, 51]], [[57, 51, 55, 48]], [[57, 51, 55, 51]], [[57, 51, 55, 57]], [53, 53, 53] :: NoLegs.members]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let rule80A ← readOptional [52, 55] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let auctionType ← readOptional [57, 51, 55, 51] tokens
  let auctionDuration ← readOptional [57, 51, 55, 57] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, rule80A, text, timeInForce, transactTime, execBroker, allocAccount, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, priceProtectionScope, stockLegGiveUp, specialOrdType, exposureFlag, auctionID, auctionType, auctionDuration, noLegs }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
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
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have auctionDuration := readOptional_part [57, 51, 55, 57] record.auctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, account, clOrdID, execInst, orderQty, ordType, price, rule80A, text, timeInForce, transactTime, execBroker, allocAccount, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, priceProtectionScope, stockLegGiveUp, specialOrdType, exposureFlag, auctionID, auctionType, auctionDuration, noLegs, some_bind] <;> rfl

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Terminated 1  -- tag 77
  allocAccount : Option (Terminated 1)  -- tag 79
  stopPx : Option (Terminated 1)  -- tag 99
  maxFloor : Option (Terminated 1)  -- tag 111
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  maturityDate : Terminated 1  -- tag 541
  routingStrategy : Option (Terminated 1)  -- tag 847
  displayWhen : Option (Terminated 1)  -- tag 1083
  displayRange : Option (Terminated 1)  -- tag 8020
  exposureFlag : Option (Terminated 1)  -- tag 9203
  brokerPCT : Option (Terminated 1)  -- tag 9204
  rFPID : Option (Terminated 1)  -- tag 9210
  rFPInstr : Option (Terminated 1)  -- tag 9211
  auctionID : Option (Terminated 1)  -- tag 9370
  auctionType : Option (Terminated 1)  -- tag 9373
  auctionDuration : Option (Terminated 1)  -- tag 9379
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.required [55, 55] record.openClose,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [53, 52, 49] record.maturityDate,
   Part.optional [56, 52, 55] record.routingStrategy,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 50, 48, 52] record.brokerPCT,
   Part.optional [57, 50, 49, 48] record.rFPID,
   Part.optional [57, 50, 49, 49] record.rFPInstr,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 57] record.auctionDuration,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[55, 57]], [[57, 57]], [[49, 49, 49]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[53, 52, 49]], [[56, 52, 55]], [[49, 48, 56, 51]], [[56, 48, 50, 48]], [[57, 50, 48, 51]], [[57, 50, 48, 52]], [[57, 50, 49, 48]], [[57, 50, 49, 49]], [[57, 51, 55, 48]], [[57, 51, 55, 51]], [[57, 51, 55, 57]], [[57, 48, 52, 51]], [[57, 48, 52, 52]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let routingStrategy ← readOptional [56, 52, 55] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let brokerPCT ← readOptional [57, 50, 48, 52] tokens
  let rFPID ← readOptional [57, 50, 49, 48] tokens
  let rFPInstr ← readOptional [57, 50, 49, 49] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let auctionType ← readOptional [57, 51, 55, 51] tokens
  let auctionDuration ← readOptional [57, 51, 55, 57] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, allocAccount, stopPx, maxFloor, putOrCall, strikePrice, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, maturityDate, routingStrategy, displayWhen, displayRange, exposureFlag, brokerPCT, rFPID, rFPInstr, auctionID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
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
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have routingStrategy := readOptional_part [56, 52, 55] record.routingStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have brokerPCT := readOptional_part [57, 50, 48, 52] record.brokerPCT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have rFPID := readOptional_part [57, 50, 49, 48] record.rFPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have rFPInstr := readOptional_part [57, 50, 49, 49] record.rFPInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have auctionDuration := readOptional_part [57, 51, 55, 57] record.auctionDuration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, execInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, allocAccount, stopPx, maxFloor, putOrCall, strikePrice, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, maturityDate, routingStrategy, displayWhen, displayRange, exposureFlag, brokerPCT, rFPID, rFPInstr, auctionID, auctionType, auctionDuration, stepUpPriceType, stepUpPrice, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Terminated 1  -- tag 77
  allocAccount : Option (Terminated 1)  -- tag 79
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  maturityDate : Terminated 1  -- tag 541
  displayWhen : Option (Terminated 1)  -- tag 1083
  displayRange : Option (Terminated 1)  -- tag 8020
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.required [55, 55] record.openClose,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [53, 52, 49] record.maturityDate,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[55, 57]], [[57, 57]], [[49, 49, 48]], [[49, 49, 49]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[53, 52, 49]], [[49, 48, 56, 51]], [[56, 48, 50, 48]], [[57, 48, 52, 51]], [[57, 48, 52, 52]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  pure { account, clOrdID, execInst, orderID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, allocAccount, stopPx, minQty, maxFloor, putOrCall, strikePrice, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, maturityDate, displayWhen, displayRange, stepUpPriceType, stepUpPrice }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, execInst, orderID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, allocAccount, stopPx, minQty, maxFloor, putOrCall, strikePrice, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, maturityDate, displayWhen, displayRange, stepUpPriceType, stepUpPrice, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  orderQty : Option (Terminated 1)  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Terminated 1  -- tag 60
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityDate : Option (Terminated 1)  -- tag 541
  noLegs : List NoLegs  -- tag 555

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 56]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52, 49]], [53, 53, 53] :: NoLegs.members]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readOptional [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  pure { clOrdID, orderQty, origClOrdID, side, symbol, transactTime, putOrCall, strikePrice, maturityDate, noLegs }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, orderQty, origClOrdID, side, symbol, transactTime, putOrCall, strikePrice, maturityDate, noLegs, some_bind] <;> rfl

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

inductive Message where
  | allocation (header : Header) (r0 : Allocation)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | memberKillSwitch (header : Header) (r0 : MemberKillSwitch)
  | multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace)
  | newOrderCross (header : Header) (r0 : NewOrderCross)
  | newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .allocation header r0 => ⟨[51, 53], ⟨[74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .memberKillSwitch header r0 => ⟨[51, 53], ⟨[85, 68, 65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegOrderCancelReplace header r0 => ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCross header r0 => ⟨[51, 53], ⟨[115], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCrossMultileg header r0 => ⟨[51, 53], ⟨[65, 115], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [74] then
        if known (Header.tags ++ Allocation.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Allocation.decode rest
          pure (.allocation header r0)
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
      else if token.value.val = [85, 68, 65] then
        if known (Header.tags ++ MemberKillSwitch.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MemberKillSwitch.decode rest
          pure (.memberKillSwitch header r0)
        else none
      else if token.value.val = [65, 67] then
        if known (Header.tags ++ MultilegOrderCancelReplace.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MultilegOrderCancelReplace.decode rest
          pure (.multilegOrderCancelReplace header r0)
        else none
      else if token.value.val = [115] then
        if known (Header.tags ++ NewOrderCross.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCross.decode rest
          pure (.newOrderCross header r0)
        else none
      else if token.value.val = [65, 115] then
        if known (Header.tags ++ NewOrderCrossMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCrossMultileg.decode rest
          pure (.newOrderCrossMultileg header r0)
        else none
      else if token.value.val = [65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
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
      else none
    else none

theorem Message.decode_allocation (header : Header) (r0 : Allocation) :
    Message.decode (Message.tokens (.allocation header r0)) = some (.allocation header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Allocation.tags) rfl rfl (by decide +kernel))
  have c1 := Allocation.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Allocation.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Allocation.tags) rfl
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

theorem Message.decode_memberKillSwitch (header : Header) (r0 : MemberKillSwitch) :
    Message.decode (Message.tokens (.memberKillSwitch header r0)) = some (.memberKillSwitch header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitch.tags) rfl rfl (by decide +kernel))
  have c1 := MemberKillSwitch.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitch.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitch.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decode (Message.tokens (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) rfl rfl (by decide +kernel))
  have c1 := MultilegOrderCancelReplace.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplace.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decode (Message.tokens (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCross.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg) :
    Message.decode (Message.tokens (.newOrderCrossMultileg header r0)) = some (.newOrderCrossMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCrossMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCrossMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCrossMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCrossMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | allocation header r0 => exact Message.decode_allocation header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | memberKillSwitch header r0 => exact Message.decode_memberKillSwitch header r0
  | multilegOrderCancelReplace header r0 => exact Message.decode_multilegOrderCancelReplace header r0
  | newOrderCross header r0 => exact Message.decode_newOrderCross header r0
  | newOrderCrossMultileg header r0 => exact Message.decode_newOrderCrossMultileg header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_allocation (header : Header) (r0 : Allocation) :
    Message.decodeBytes (Message.encode (.allocation header r0)) = some (.allocation header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Allocation.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocation header r0

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

theorem Message.decodeBytes_memberKillSwitch (header : Header) (r0 : MemberKillSwitch) :
    Message.decodeBytes (Message.encode (.memberKillSwitch header r0)) = some (.memberKillSwitch header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68, 65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitch.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_memberKillSwitch header r0

theorem Message.decodeBytes_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decodeBytes (Message.encode (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplace.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_multilegOrderCancelReplace header r0

theorem Message.decodeBytes_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decodeBytes (Message.encode (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[115], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCross header r0

theorem Message.decodeBytes_newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg) :
    Message.decodeBytes (Message.encode (.newOrderCrossMultileg header r0)) = some (.newOrderCrossMultileg header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 115], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderCrossMultileg.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCrossMultileg header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | allocation header r0 => exact Message.decodeBytes_allocation header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | memberKillSwitch header r0 => exact Message.decodeBytes_memberKillSwitch header r0
  | multilegOrderCancelReplace header r0 => exact Message.decodeBytes_multilegOrderCancelReplace header r0
  | newOrderCross header r0 => exact Message.decodeBytes_newOrderCross header r0
  | newOrderCrossMultileg header r0 => exact Message.decodeBytes_newOrderCrossMultileg header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqPhlxoptionsOrderentryFixV134Client
