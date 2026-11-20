import Wire

/-!
# Chicago Board Options Exchange Order Entry v3.39, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBxeequitiesOrderentryFixV339Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

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

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 54] record.targetCompID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 50, 57] record.deliverToSubID (by decide) (by decide))
              (paired_none pairing))))))))))))

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

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 53, 50] record.partyRole (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 51, 55, 54] record.partyRoleQualifier (by decide) (by decide))
      (paired_none pairing))))

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

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Option (Terminated 1)  -- tag 6
  clOrdID : Option (Terminated 1)  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  currency : Option (Terminated 1)  -- tag 15
  execID : Option (Terminated 1)  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
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
  settlType : Option (Terminated 1)  -- tag 63
  settlDate : Option (Terminated 1)  -- tag 64
  ordRejReason : Option (Terminated 1)  -- tag 103
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  execType : Option (Terminated 1)  -- tag 150
  leavesQty : Option (Terminated 1)  -- tag 151
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  securityExchange : Option (Terminated 1)  -- tag 207
  contraBroker : Option (Terminated 1)  -- tag 375
  execRestatementReason : Option (Terminated 1)  -- tag 378
  noContraBrokers : Option (Terminated 1)  -- tag 382
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  noPartyIDs : List NoPartyIDs  -- tag 453
  settlPrice : Option (Terminated 1)  -- tag 730
  orderOrigination : Option (Terminated 1)  -- tag 1724
  centralCounterparty : Option (Terminated 1)  -- tag 7772
  trdRegPublicationReasons : Option (Terminated 1)  -- tag 8013
  orderAttributeTypes : Option (Terminated 1)  -- tag 8015
  tradingVenueRegTradeId : Option (Terminated 1)  -- tag 8016
  extExecInst : Option (Terminated 1)  -- tag 9416
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  feeCode : Option (Terminated 1)  -- tag 9882

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
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
   Part.optional [54, 51] record.settlType,
   Part.optional [54, 52] record.settlDate,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [55, 55, 55, 50] record.centralCounterparty,
   Part.optional [56, 48, 49, 51] record.trdRegPublicationReasons,
   Part.optional [56, 48, 49, 53] record.orderAttributeTypes,
   Part.optional [56, 48, 49, 54] record.tradingVenueRegTradeId,
   Part.optional [57, 52, 49, 54] record.extExecInst,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [57, 56, 56, 50] record.feeCode]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 53]], [[49, 55]], [[49, 56]], [[50, 48]], [[50, 50]], [[50, 57]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 49]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 51]], [[54, 52]], [[49, 48, 51]], [[49, 49, 49]], [[49, 50, 54]], [[49, 53, 48]], [[49, 53, 49]], [[49, 57, 56]], [[50, 48, 55]], [[51, 55, 53]], [[51, 55, 56]], [[51, 56, 50]], [[52, 51, 57]], [[52, 52, 48]], [52, 53, 51] :: NoPartyIDs.members, [[55, 51, 48]], [[49, 55, 50, 52]], [[55, 55, 55, 50]], [[56, 48, 49, 51]], [[56, 48, 49, 53]], [[56, 48, 49, 54]], [[57, 52, 49, 54]], [[57, 55, 51, 48]], [[57, 56, 56, 50]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let avgPx ← readOptional [54] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let currency ← readOptional [49, 53] tokens
  let execID ← readOptional [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
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
  let settlType ← readOptional [54, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let centralCounterparty ← readOptional [55, 55, 55, 50] tokens
  let trdRegPublicationReasons ← readOptional [56, 48, 49, 51] tokens
  let orderAttributeTypes ← readOptional [56, 48, 49, 53] tokens
  let tradingVenueRegTradeId ← readOptional [56, 48, 49, 54] tokens
  let extExecInst ← readOptional [57, 52, 49, 54] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { account, avgPx, clOrdID, cumQty, currency, execID, execInst, execTransType, iDSource, lastCapacity, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, settlType, settlDate, ordRejReason, maxFloor, expireTime, execType, leavesQty, secondaryOrderID, securityExchange, contraBroker, execRestatementReason, noContraBrokers, clearingFirm, clearingAccount, noPartyIDs, settlPrice, orderOrigination, centralCounterparty, trdRegPublicationReasons, orderAttributeTypes, tradingVenueRegTradeId, extExecInst, tradeLiquidityIndicator, feeCode }

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
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have centralCounterparty := readOptional_part [55, 55, 55, 50] record.centralCounterparty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have trdRegPublicationReasons := readOptional_part [56, 48, 49, 51] record.trdRegPublicationReasons tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have orderAttributeTypes := readOptional_part [56, 48, 49, 53] record.orderAttributeTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have tradingVenueRegTradeId := readOptional_part [56, 48, 49, 54] record.tradingVenueRegTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have extExecInst := readOptional_part [57, 52, 49, 54] record.extExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, cumQty, currency, execID, execInst, execTransType, iDSource, lastCapacity, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, settlType, settlDate, ordRejReason, maxFloor, expireTime, execType, leavesQty, secondaryOrderID, securityExchange, contraBroker, execRestatementReason, noContraBrokers, clearingFirm, clearingAccount, noPartyIDs, settlPrice, orderOrigination, centralCounterparty, trdRegPublicationReasons, orderAttributeTypes, tradingVenueRegTradeId, extExecInst, tradeLiquidityIndicator, feeCode, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54] record.avgPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 55] record.execID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48] record.execTransType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastMkt (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastShares (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [51, 57] record.ordStatus (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.settlDate (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [51, 56, 50] record.noContraBrokers (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
                                         (paired_cons pairing _ _ (paired_optional pairing [55, 51, 48] record.settlPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.orderOrigination (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [55, 55, 55, 50] record.centralCounterparty (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 51] record.trdRegPublicationReasons (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 53] record.orderAttributeTypes (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 54] record.tradingVenueRegTradeId (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [57, 52, 49, 54] record.extExecInst (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [57, 55, 51, 48] record.tradeLiquidityIndicator (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.feeCode (by decide) (by decide))
                                                  (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))

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

theorem CancelReject.taken (record : CancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 57] record.ordStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
          (paired_none pairing))))))))

structure TradeCancelCorrect where
  clOrdID : Option (Terminated 1)  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
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
  settlType : Option (Terminated 1)  -- tag 63
  settlDate : Option (Terminated 1)  -- tag 64
  securityExchange : Option (Terminated 1)  -- tag 207
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  settlPrice : Option (Terminated 1)  -- tag 730
  correctedSize : Option (Terminated 1)  -- tag 6655
  tradingVenueRegTradeId : Option (Terminated 1)  -- tag 8016
  correctedPrice : Option (Terminated 1)  -- tag 9620
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730

def TradeCancelCorrect.parts (record : TradeCancelCorrect) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
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
   Part.optional [54, 51] record.settlType,
   Part.optional [54, 52] record.settlDate,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.optional [54, 54, 53, 53] record.correctedSize,
   Part.optional [56, 48, 49, 54] record.tradingVenueRegTradeId,
   Part.optional [57, 54, 50, 48] record.correctedPrice,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator]

def TradeCancelCorrect.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 53]], [[49, 55]], [[49, 57]], [[50, 48]], [[50, 50]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[52, 50]], [[52, 56]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 51]], [[54, 52]], [[50, 48, 55]], [[52, 51, 57]], [[52, 52, 48]], [[55, 51, 48]], [[54, 54, 53, 53]], [[56, 48, 49, 54]], [[57, 54, 50, 48]], [[57, 55, 51, 48]]]

theorem TradeCancelCorrect.shape (record : TradeCancelCorrect) : record.parts.map Part.tags = TradeCancelCorrect.tags := rfl

def TradeCancelCorrect.decode (tokens : List Token) : Option TradeCancelCorrect := do
  let clOrdID ← readOptional [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
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
  let settlType ← readOptional [54, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let correctedSize ← readOptional [54, 54, 53, 53] tokens
  let tradingVenueRegTradeId ← readOptional [56, 48, 49, 54] tokens
  let correctedPrice ← readOptional [57, 54, 50, 48] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  pure { clOrdID, currency, execID, execRefID, execTransType, iDSource, lastMkt, lastPx, lastShares, orderID, origTime, securityID, side, symbol, transactTime, settlType, settlDate, securityExchange, clearingFirm, clearingAccount, settlPrice, correctedSize, tradingVenueRegTradeId, correctedPrice, tradeLiquidityIndicator }

theorem TradeCancelCorrect.decode_agrees (record : TradeCancelCorrect) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCancelCorrect.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCancelCorrect.decode tokens = some record := by
  have distinct : TradeCancelCorrect.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have origTime := readOptional_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have correctedSize := readOptional_part [54, 54, 53, 53] record.correctedSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have tradingVenueRegTradeId := readOptional_part [56, 48, 49, 54] record.tradingVenueRegTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have correctedPrice := readOptional_part [57, 54, 50, 48] record.correctedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [TradeCancelCorrect.decode, clOrdID, currency, execID, execRefID, execTransType, iDSource, lastMkt, lastPx, lastShares, orderID, origTime, securityID, side, symbol, transactTime, settlType, settlDate, securityExchange, clearingFirm, clearingAccount, settlPrice, correctedSize, tradingVenueRegTradeId, correctedPrice, tradeLiquidityIndicator, some_bind] <;> rfl

theorem TradeCancelCorrect.taken (record : TradeCancelCorrect) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 55] record.execID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastMkt (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastShares (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 50] record.origTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.settlDate (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [55, 51, 48] record.settlPrice (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [54, 54, 53, 53] record.correctedSize (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 54] record.tradingVenueRegTradeId (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [57, 54, 50, 48] record.correctedPrice (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [57, 55, 51, 48] record.tradeLiquidityIndicator (by decide) (by decide))
                           (paired_none pairing)))))))))))))))))))))))))

inductive Message where
  | executionReport (header : Header) (r0 : ExecutionReport)
  | cancelReject (header : Header) (r0 : CancelReject)
  | tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect)

def Message.tokens : Message → List Token
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCancelCorrect header r0 => ⟨[51, 53], [85, 67, 67]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value = [57] then
        if known (Header.tags ++ CancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReject.decode rest
          pure (.cancelReject header r0)
        else none
      else if token.value = [85, 67, 67] then
        if known (Header.tags ++ TradeCancelCorrect.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCancelCorrect.decode rest
          pure (.tradeCancelCorrect header r0)
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | cancelReject header r0 => exact Message.decode_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decode_tradeCancelCorrect header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ExecutionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decodeBytes (Message.encode (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (CancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReject header r0

theorem Message.decodeBytes_tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect) :
    Message.decodeBytes (Message.encode (.tradeCancelCorrect header r0)) = some (.tradeCancelCorrect header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCancelCorrect.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCancelCorrect header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | cancelReject header r0 => exact Message.decodeBytes_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decodeBytes_tradeCancelCorrect header r0

/-- BeginString as the venue states it: one of FIX.4.2, FIX.4.4, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 50], [70, 73, 88, 46, 52, 46, 52]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.CboeBxeequitiesOrderentryFixV339Exchange
