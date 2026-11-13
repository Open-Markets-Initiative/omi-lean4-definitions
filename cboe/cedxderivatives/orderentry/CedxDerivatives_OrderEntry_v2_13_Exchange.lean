import Wire

/-!
# Chicago Board Options Exchange Order Entry v2.13, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCedxderivativesOrderentryFixV213Exchange

structure Header where
  msgSeqNum : Option (Terminated 1)  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Option (Terminated 1)  -- tag 49
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.optional [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readOptional [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readOptional_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderCompID := readOptional_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID, some_bind] <;> rfl

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

structure NoAffectedOrders where
  affectedOrigClOrdID : Terminated 1  -- tag 1824

def NoAffectedOrders.parts (record : NoAffectedOrders) : List Part :=
  [Part.required [49, 56, 50, 52] record.affectedOrigClOrdID]

def NoAffectedOrders.tags : List (List (List UInt8)) :=
  [[[49, 56, 50, 52]]]

theorem NoAffectedOrders.shape (record : NoAffectedOrders) : record.parts.map Part.tags = NoAffectedOrders.tags := rfl

def NoAffectedOrders.decode (tokens : List Token) : Option NoAffectedOrders := do
  let affectedOrigClOrdID ← readRequired [49, 56, 50, 52] tokens
  pure { affectedOrigClOrdID }

theorem NoAffectedOrders.decode_agrees (record : NoAffectedOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAffectedOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAffectedOrders.decode tokens = some record := by
  have distinct : NoAffectedOrders.tags.flatten.Nodup := by decide +kernel
  have affectedOrigClOrdID := readRequired_part [49, 56, 50, 52] record.affectedOrigClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoAffectedOrders.decode, affectedOrigClOrdID, some_bind] <;> rfl

def NoAffectedOrders.members : List (List UInt8) := NoAffectedOrders.tags.flatten

def NoAffectedOrders.encode (entry : NoAffectedOrders) : List Token := encodeParts entry.parts

theorem NoAffectedOrders.decode_encode (entry : NoAffectedOrders) : NoAffectedOrders.decode entry.encode = some entry :=
  NoAffectedOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAffectedOrders.within (entry : NoAffectedOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoAffectedOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAffectedOrders.shape] at this

theorem NoAffectedOrders.led (entry : NoAffectedOrders) : Lead [49, 56, 50, 52] entry.encode :=
  lead_parts [49, 56, 50, 52] entry.affectedOrigClOrdID _ NoAffectedOrders.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legRefID : Terminated 1  -- tag 654
  legSymbol : Option (Terminated 1)  -- tag 600
  legRatioQty : Option (Terminated 1)  -- tag 623
  legSide : Option (Terminated 1)  -- tag 624
  legPrice : Option (Terminated 1)  -- tag 566
  legPositionEffect : Option (Terminated 1)  -- tag 564

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 53, 52] record.legRefID,
   Part.optional [54, 48, 48] record.legSymbol,
   Part.optional [54, 50, 51] record.legRatioQty,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [53, 54, 54] record.legPrice,
   Part.optional [53, 54, 52] record.legPositionEffect]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 53, 52]], [[54, 48, 48]], [[54, 50, 51]], [[54, 50, 52]], [[53, 54, 54]], [[53, 54, 52]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legRefID ← readRequired [54, 53, 52] tokens
  let legSymbol ← readOptional [54, 48, 48] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  let legPositionEffect ← readOptional [53, 54, 52] tokens
  pure { legRefID, legSymbol, legRatioQty, legSide, legPrice, legPositionEffect }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSymbol := readOptional_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legPositionEffect := readOptional_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NoLegs.decode, legRefID, legSymbol, legRatioQty, legSide, legPrice, legPositionEffect, some_bind] <;> rfl

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

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Option (Terminated 1)  -- tag 6
  clOrdID : Option (Terminated 1)  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Option (Terminated 1)  -- tag 17
  execTransType : Option (Terminated 1)  -- tag 20
  iDSource : Option (Terminated 1)  -- tag 22
  lastCapacity : Option (Terminated 1)  -- tag 29
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Option (Terminated 1)  -- tag 38
  ordStatus : Option (Terminated 1)  -- tag 39
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Option (Terminated 1)  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  ordRejReason : Option (Terminated 1)  -- tag 103
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  execType : Option (Terminated 1)  -- tag 150
  leavesQty : Option (Terminated 1)  -- tag 151
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  contraBroker : Option (Terminated 1)  -- tag 375
  execRestatementReason : Option (Terminated 1)  -- tag 378
  noContraBrokers : Option (Terminated 1)  -- tag 382
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  noPartyIDs : List NoPartyIDs  -- tag 453
  multilegReportingType : Option (Terminated 1)  -- tag 442
  secondaryExecID : Option (Terminated 1)  -- tag 527
  noAffectedOrders : List NoAffectedOrders  -- tag 534
  crossID : Option (Terminated 1)  -- tag 548
  crossType : Option (Terminated 1)  -- tag 549
  crossPrioritization : Option (Terminated 1)  -- tag 550
  noLegs : List NoLegs  -- tag 555
  accountType : Option (Terminated 1)  -- tag 581
  custOrderHandlingInst : Option (Terminated 1)  -- tag 1031
  orderOrigination : Option (Terminated 1)  -- tag 1724
  drillThruProtection : Option (Terminated 1)  -- tag 6253
  crossExclusionIndicator : Option (Terminated 1)  -- tag 6438
  massCancelID : Option (Terminated 1)  -- tag 7695
  cancelledOrderCount : Option (Terminated 1)  -- tag 7696
  centralCounterparty : Option (Terminated 1)  -- tag 7772
  orderAttributeTypes : Option (Terminated 1)  -- tag 8015
  routingInst : Option (Terminated 1)  -- tag 9303
  auctionID : Option (Terminated 1)  -- tag 9370
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  feeCode : Option (Terminated 1)  -- tag 9882
  subreasonText : Option (Terminated 1)  -- tag 22058

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.optional [49, 55] record.execID,
   Part.optional [50, 48] record.execTransType,
   Part.optional [50, 50] record.iDSource,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 55] record.orderID,
   Part.optional [51, 56] record.orderQty,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.group [53, 51, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within record.noAffectedOrders,
   Part.optional [53, 52, 56] record.crossID,
   Part.optional [53, 52, 57] record.crossType,
   Part.optional [53, 53, 48] record.crossPrioritization,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [49, 48, 51, 49] record.custOrderHandlingInst,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [54, 50, 53, 51] record.drillThruProtection,
   Part.optional [54, 52, 51, 56] record.crossExclusionIndicator,
   Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.optional [55, 54, 57, 54] record.cancelledOrderCount,
   Part.optional [55, 55, 55, 50] record.centralCounterparty,
   Part.optional [56, 48, 49, 53] record.orderAttributeTypes,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [57, 56, 56, 50] record.feeCode,
   Part.optional [50, 50, 48, 53, 56] record.subreasonText]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[50, 50]], [[50, 57]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 49]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[57, 57]], [[49, 48, 51]], [[49, 49, 48]], [[49, 50, 54]], [[49, 53, 48]], [[49, 53, 49]], [[49, 57, 56]], [[51, 55, 53]], [[51, 55, 56]], [[51, 56, 50]], [[52, 51, 57]], [[52, 52, 48]], [52, 53, 51] :: NoPartyIDs.members, [[52, 52, 50]], [[53, 50, 55]], [53, 51, 52] :: NoAffectedOrders.members, [[53, 52, 56]], [[53, 52, 57]], [[53, 53, 48]], [53, 53, 53] :: NoLegs.members, [[53, 56, 49]], [[49, 48, 51, 49]], [[49, 55, 50, 52]], [[54, 50, 53, 51]], [[54, 52, 51, 56]], [[55, 54, 57, 53]], [[55, 54, 57, 54]], [[55, 55, 55, 50]], [[56, 48, 49, 53]], [[57, 51, 48, 51]], [[57, 51, 55, 48]], [[57, 55, 51, 48]], [[57, 56, 56, 50]], [[50, 50, 48, 53, 56]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let avgPx ← readOptional [54] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readOptional [49, 55] tokens
  let execTransType ← readOptional [50, 48] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let multilegReportingType ← readOptional [52, 52, 50] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let noAffectedOrders ← readGroup [53, 51, 52] [49, 56, 50, 52] NoAffectedOrders.members NoAffectedOrders.decode tokens
  let crossID ← readOptional [53, 52, 56] tokens
  let crossType ← readOptional [53, 52, 57] tokens
  let crossPrioritization ← readOptional [53, 53, 48] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let custOrderHandlingInst ← readOptional [49, 48, 51, 49] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let drillThruProtection ← readOptional [54, 50, 53, 51] tokens
  let crossExclusionIndicator ← readOptional [54, 52, 51, 56] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let cancelledOrderCount ← readOptional [55, 54, 57, 54] tokens
  let centralCounterparty ← readOptional [55, 55, 55, 50] tokens
  let orderAttributeTypes ← readOptional [56, 48, 49, 53] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  let subreasonText ← readOptional [50, 50, 48, 53, 56] tokens
  pure { account, avgPx, clOrdID, cumQty, execID, execTransType, iDSource, lastCapacity, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, openClose, stopPx, ordRejReason, minQty, expireTime, execType, leavesQty, secondaryOrderID, contraBroker, execRestatementReason, noContraBrokers, clearingFirm, clearingAccount, noPartyIDs, multilegReportingType, secondaryExecID, noAffectedOrders, crossID, crossType, crossPrioritization, noLegs, accountType, custOrderHandlingInst, orderOrigination, drillThruProtection, crossExclusionIndicator, massCancelID, cancelledOrderCount, centralCounterparty, orderAttributeTypes, routingInst, auctionID, tradeLiquidityIndicator, feeCode, subreasonText }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have multilegReportingType := readOptional_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have noAffectedOrders := readGroup_part [53, 51, 52] [49, 56, 50, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within NoAffectedOrders.decode NoAffectedOrders.decode_encode NoAffectedOrders.led record.noAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have crossID := readOptional_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have crossType := readOptional_part [53, 52, 57] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have crossPrioritization := readOptional_part [53, 53, 48] record.crossPrioritization tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have custOrderHandlingInst := readOptional_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have drillThruProtection := readOptional_part [54, 50, 53, 51] record.drillThruProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have crossExclusionIndicator := readOptional_part [54, 52, 51, 56] record.crossExclusionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have cancelledOrderCount := readOptional_part [55, 54, 57, 54] record.cancelledOrderCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have centralCounterparty := readOptional_part [55, 55, 55, 50] record.centralCounterparty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have orderAttributeTypes := readOptional_part [56, 48, 49, 53] record.orderAttributeTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have subreasonText := readOptional_part [50, 50, 48, 53, 56] record.subreasonText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, cumQty, execID, execTransType, iDSource, lastCapacity, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, openClose, stopPx, ordRejReason, minQty, expireTime, execType, leavesQty, secondaryOrderID, contraBroker, execRestatementReason, noContraBrokers, clearingFirm, clearingAccount, noPartyIDs, multilegReportingType, secondaryExecID, noAffectedOrders, crossID, crossType, crossPrioritization, noLegs, accountType, custOrderHandlingInst, orderOrigination, drillThruProtection, crossExclusionIndicator, massCancelID, cancelledOrderCount, centralCounterparty, orderAttributeTypes, routingInst, auctionID, tradeLiquidityIndicator, feeCode, subreasonText, some_bind] <;> rfl

structure CancelReject where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Option (Terminated 1)  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  ordStatus : Option (Terminated 1)  -- tag 39
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  cxlRejReason : Option (Terminated 1)  -- tag 102
  cxlRejResponseTo : Option (Terminated 1)  -- tag 434

def CancelReject.parts (record : CancelReject) : List Part :=
  [Part.optional [49] record.account,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [52, 51, 52] record.cxlRejResponseTo]

def CancelReject.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[49, 48, 50]], [[52, 51, 52]]]

theorem CancelReject.shape (record : CancelReject) : record.parts.map Part.tags = CancelReject.tags := rfl

def CancelReject.decode (tokens : List Token) : Option CancelReject := do
  let account ← readOptional [49] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let cxlRejResponseTo ← readOptional [52, 51, 52] tokens
  pure { account, clOrdID, orderID, ordStatus, origClOrdID, text, cxlRejReason, cxlRejResponseTo }

theorem CancelReject.decode_agrees (record : CancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelReject.decode tokens = some record := by
  have distinct : CancelReject.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cxlRejResponseTo := readOptional_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [CancelReject.decode, account, clOrdID, orderID, ordStatus, origClOrdID, text, cxlRejReason, cxlRejResponseTo, some_bind] <;> rfl

structure TradeCancelCorrect where
  clOrdID : Option (Terminated 1)  -- tag 11
  execID : Option (Terminated 1)  -- tag 17
  execRefID : Option (Terminated 1)  -- tag 19
  execTransType : Option (Terminated 1)  -- tag 20
  iDSource : Option (Terminated 1)  -- tag 22
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  orderID : Option (Terminated 1)  -- tag 37
  origTime : Option (Terminated 1)  -- tag 42
  securityID : Option (Terminated 1)  -- tag 48
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Option (Terminated 1)  -- tag 77
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  settlPrice : Option (Terminated 1)  -- tag 730
  correctedSize : Option (Terminated 1)  -- tag 6655
  correctedPrice : Option (Terminated 1)  -- tag 9620
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730

def TradeCancelCorrect.parts (record : TradeCancelCorrect) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 55] record.execID,
   Part.optional [49, 57] record.execRefID,
   Part.optional [50, 48] record.execTransType,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 50] record.origTime,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 55] record.openClose,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.optional [54, 54, 53, 53] record.correctedSize,
   Part.optional [57, 54, 50, 48] record.correctedPrice,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator]

def TradeCancelCorrect.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 55]], [[49, 57]], [[50, 48]], [[50, 50]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[52, 50]], [[52, 56]], [[53, 52]], [[53, 53]], [[54, 48]], [[55, 55]], [[52, 51, 57]], [[52, 52, 48]], [[55, 51, 48]], [[54, 54, 53, 53]], [[57, 54, 50, 48]], [[57, 55, 51, 48]]]

theorem TradeCancelCorrect.shape (record : TradeCancelCorrect) : record.parts.map Part.tags = TradeCancelCorrect.tags := rfl

def TradeCancelCorrect.decode (tokens : List Token) : Option TradeCancelCorrect := do
  let clOrdID ← readOptional [49, 49] tokens
  let execID ← readOptional [49, 55] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execTransType ← readOptional [50, 48] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let origTime ← readOptional [52, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let correctedSize ← readOptional [54, 54, 53, 53] tokens
  let correctedPrice ← readOptional [57, 54, 50, 48] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  pure { clOrdID, execID, execRefID, execTransType, iDSource, lastMkt, lastPx, lastShares, orderID, origTime, securityID, side, symbol, transactTime, openClose, clearingFirm, clearingAccount, settlPrice, correctedSize, correctedPrice, tradeLiquidityIndicator }

theorem TradeCancelCorrect.decode_agrees (record : TradeCancelCorrect) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCancelCorrect.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCancelCorrect.decode tokens = some record := by
  have distinct : TradeCancelCorrect.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origTime := readOptional_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have correctedSize := readOptional_part [54, 54, 53, 53] record.correctedSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have correctedPrice := readOptional_part [57, 54, 50, 48] record.correctedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [TradeCancelCorrect.decode, clOrdID, execID, execRefID, execTransType, iDSource, lastMkt, lastPx, lastShares, orderID, origTime, securityID, side, symbol, transactTime, openClose, clearingFirm, clearingAccount, settlPrice, correctedSize, correctedPrice, tradeLiquidityIndicator, some_bind] <;> rfl

structure SecurityDefinitionOptionsOnly where
  clOrdID : Option (Terminated 1)  -- tag 11
  symbol : Option (Terminated 1)  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  securityResponseType : Option (Terminated 1)  -- tag 323
  noLegs : List NoLegs  -- tag 555
  noOfSecurities : Option (Terminated 1)  -- tag 8641

def SecurityDefinitionOptionsOnly.parts (record : SecurityDefinitionOptionsOnly) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [51, 50, 51] record.securityResponseType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [56, 54, 52, 49] record.noOfSecurities]

def SecurityDefinitionOptionsOnly.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 53]], [[53, 56]], [[51, 50, 51]], [53, 53, 53] :: NoLegs.members, [[56, 54, 52, 49]]]

theorem SecurityDefinitionOptionsOnly.shape (record : SecurityDefinitionOptionsOnly) : record.parts.map Part.tags = SecurityDefinitionOptionsOnly.tags := rfl

def SecurityDefinitionOptionsOnly.decode (tokens : List Token) : Option SecurityDefinitionOptionsOnly := do
  let clOrdID ← readOptional [49, 49] tokens
  let symbol ← readOptional [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let securityResponseType ← readOptional [51, 50, 51] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  let noOfSecurities ← readOptional [56, 54, 52, 49] tokens
  pure { clOrdID, symbol, text, securityResponseType, noLegs, noOfSecurities }

theorem SecurityDefinitionOptionsOnly.decode_agrees (record : SecurityDefinitionOptionsOnly) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionOptionsOnly.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionOptionsOnly.decode tokens = some record := by
  have distinct : SecurityDefinitionOptionsOnly.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityResponseType := readOptional_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noOfSecurities := readOptional_part [56, 54, 52, 49] record.noOfSecurities tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [SecurityDefinitionOptionsOnly.decode, clOrdID, symbol, text, securityResponseType, noLegs, noOfSecurities, some_bind] <;> rfl

inductive Message where
  | executionReport (header : Header) (r0 : ExecutionReport)
  | cancelReject (header : Header) (r0 : CancelReject)
  | tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect)
  | securityDefinitionOptionsOnly (header : Header) (r0 : SecurityDefinitionOptionsOnly)

def Message.tokens : Message → List Token
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCancelCorrect header r0 => ⟨[51, 53], ⟨[85, 67, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionOptionsOnly header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ CancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReject.decode rest
          pure (.cancelReject header r0)
        else none
      else if token.value.val = [85, 67, 67] then
        if known (Header.tags ++ TradeCancelCorrect.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCancelCorrect.decode rest
          pure (.tradeCancelCorrect header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinitionOptionsOnly.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionOptionsOnly.decode rest
          pure (.securityDefinitionOptionsOnly header r0)
        else none
      else none
    else none

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decode (Message.tokens (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := CancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect) :
    Message.decode (Message.tokens (.tradeCancelCorrect header r0)) = some (.tradeCancelCorrect header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrect.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCancelCorrect.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrect.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCancelCorrect.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionOptionsOnly (header : Header) (r0 : SecurityDefinitionOptionsOnly) :
    Message.decode (Message.tokens (.securityDefinitionOptionsOnly header r0)) = some (.securityDefinitionOptionsOnly header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionOptionsOnly.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionOptionsOnly.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionOptionsOnly.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionOptionsOnly.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | cancelReject header r0 => exact Message.decode_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decode_tradeCancelCorrect header r0
  | securityDefinitionOptionsOnly header r0 => exact Message.decode_securityDefinitionOptionsOnly header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decodeBytes (Message.encode (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReject header r0

theorem Message.decodeBytes_tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect) :
    Message.decodeBytes (Message.encode (.tradeCancelCorrect header r0)) = some (.tradeCancelCorrect header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 67, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCancelCorrect.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCancelCorrect header r0

theorem Message.decodeBytes_securityDefinitionOptionsOnly (header : Header) (r0 : SecurityDefinitionOptionsOnly) :
    Message.decodeBytes (Message.encode (.securityDefinitionOptionsOnly header r0)) = some (.securityDefinitionOptionsOnly header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionOptionsOnly.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionOptionsOnly header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | cancelReject header r0 => exact Message.decodeBytes_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decodeBytes_tradeCancelCorrect header r0
  | securityDefinitionOptionsOnly header r0 => exact Message.decodeBytes_securityDefinitionOptionsOnly header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCedxderivativesOrderentryFixV213Exchange
