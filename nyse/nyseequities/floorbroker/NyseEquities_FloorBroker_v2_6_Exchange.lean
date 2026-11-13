import Wire

/-!
# New York Stock Exchange NYSE Pillar Gateway Floor Broker v2.6, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NyseNyseequitiesFloorbrokerFixV26Exchange

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  delivertoCompID : Option (Terminated 1)  -- tag 128

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.delivertoCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let delivertoCompID ← readOptional [49, 50, 56] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, delivertoCompID }

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
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have delivertoCompID := readOptional_part [49, 50, 56] record.delivertoCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, delivertoCompID, some_bind] <;> rfl

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execRefID : Option (Terminated 1)  -- tag 19
  execTransType : Terminated 1  -- tag 20
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  clientID : Option (Terminated 1)  -- tag 109
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
  execType : Terminated 1  -- tag 150
  leavesQty : Option (Terminated 1)  -- tag 151
  effectiveTime : Option (Terminated 1)  -- tag 168
  noTradingSessions : Terminated 1  -- tag 386
  tradingSessionID : Terminated 1  -- tag 336
  orderCapacity : Terminated 1  -- tag 528
  participationRate : Option (Terminated 1)  -- tag 849
  locateBroker : Option (Terminated 1)  -- tag 5700
  selfTradeType : Option (Terminated 1)  -- tag 7928
  specialOrdType : Option (Terminated 1)  -- tag 9202
  routingInst : Option (Terminated 1)  -- tag 9303
  offsetPrice : Option (Terminated 1)  -- tag 9403
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  displayedLiquidityIndicator : Option (Terminated 1)  -- tag 9426
  introducingBadgeID : Terminated 1  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  parentFirmClOrdID : Terminated 1  -- tag 9451
  interestType : Option (Terminated 1)  -- tag 9478
  dealID : Option (Terminated 1)  -- tag 9483
  dOrderAuctionPrice : Option (Terminated 1)  -- tag 9565
  liquidityIndicator : Option (Terminated 1)  -- tag 9730
  attributedQuote : Option (Terminated 1)  -- tag 20001
  proactiveIfLocked : Option (Terminated 1)  -- tag 20002
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  workingPrice : Option (Terminated 1)  -- tag 20004
  flowIndicator : Terminated 1  -- tag 20005
  workingAwayFromDisplay : Option (Terminated 1)  -- tag 20006
  unsolicitedAckType : Option (Terminated 1)  -- tag 20007
  participantType : Option (Terminated 1)  -- tag 20008
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  subIDIndicator : Option (Terminated 1)  -- tag 20013
  cATIMID : Option (Terminated 1)  -- tag 20042
  targetStrategy : Option (Terminated 1)  -- tag 20046
  f10b18 : Option (Terminated 1)  -- tag 20047
  auctionEligible : Option (Terminated 1)  -- tag 20048
  minParticpationRate : Option (Terminated 1)  -- tag 20049
  maxParticipationRate : Option (Terminated 1)  -- tag 20050
  wouldPrice : Option (Terminated 1)  -- tag 20051
  allocationFirmIntroducingBadgeID : Option (Terminated 1)  -- tag 20024
  allocationFirmMPID : Option (Terminated 1)  -- tag 20022
  refDealID : Terminated 1  -- tag 30002
  allocationIndicator : Option (Terminated 1)  -- tag 30003
  originalDealID : Option (Terminated 1)  -- tag 30006
  refExecTimestamp : Option (Terminated 1)  -- tag 30016

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 57] record.execRefID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [49, 53, 48] record.execType,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 54, 56] record.effectiveTime,
   Part.required [51, 56, 54] record.noTradingSessions,
   Part.required [51, 51, 54] record.tradingSessionID,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [56, 52, 57] record.participationRate,
   Part.optional [53, 55, 48, 48] record.locateBroker,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 48, 51] record.offsetPrice,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 50, 54] record.displayedLiquidityIndicator,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.required [57, 52, 53, 49] record.parentFirmClOrdID,
   Part.optional [57, 52, 55, 56] record.interestType,
   Part.optional [57, 52, 56, 51] record.dealID,
   Part.optional [57, 53, 54, 53] record.dOrderAuctionPrice,
   Part.optional [57, 55, 51, 48] record.liquidityIndicator,
   Part.optional [50, 48, 48, 48, 49] record.attributedQuote,
   Part.optional [50, 48, 48, 48, 50] record.proactiveIfLocked,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 48, 52] record.workingPrice,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.optional [50, 48, 48, 48, 54] record.workingAwayFromDisplay,
   Part.optional [50, 48, 48, 48, 55] record.unsolicitedAckType,
   Part.optional [50, 48, 48, 48, 56] record.participantType,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator,
   Part.optional [50, 48, 48, 52, 50] record.cATIMID,
   Part.optional [50, 48, 48, 52, 54] record.targetStrategy,
   Part.optional [50, 48, 48, 52, 55] record.f10b18,
   Part.optional [50, 48, 48, 52, 56] record.auctionEligible,
   Part.optional [50, 48, 48, 52, 57] record.minParticpationRate,
   Part.optional [50, 48, 48, 53, 48] record.maxParticipationRate,
   Part.optional [50, 48, 48, 53, 49] record.wouldPrice,
   Part.optional [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID,
   Part.optional [50, 48, 48, 50, 50] record.allocationFirmMPID,
   Part.required [51, 48, 48, 48, 50] record.refDealID,
   Part.optional [51, 48, 48, 48, 51] record.allocationIndicator,
   Part.optional [51, 48, 48, 48, 54] record.originalDealID,
   Part.optional [51, 48, 48, 49, 54] record.refExecTimestamp]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[49, 56]], [[49, 57]], [[50, 48]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 53]], [[49, 48, 57]], [[49, 49, 48]], [[49, 49, 49]], [[49, 49, 52]], [[49, 50, 54]], [[49, 53, 48]], [[49, 53, 49]], [[49, 54, 56]], [[51, 56, 54]], [[51, 51, 54]], [[53, 50, 56]], [[56, 52, 57]], [[53, 55, 48, 48]], [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 51, 48, 51]], [[57, 52, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 50, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[57, 52, 53, 49]], [[57, 52, 55, 56]], [[57, 52, 56, 51]], [[57, 53, 54, 53]], [[57, 55, 51, 48]], [[50, 48, 48, 48, 49]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 48, 52]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 55]], [[50, 48, 48, 48, 56]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 52, 50]], [[50, 48, 48, 52, 54]], [[50, 48, 48, 52, 55]], [[50, 48, 48, 52, 56]], [[50, 48, 48, 52, 57]], [[50, 48, 48, 53, 48]], [[50, 48, 48, 53, 49]], [[50, 48, 48, 50, 52]], [[50, 48, 48, 50, 50]], [[51, 48, 48, 48, 50]], [[51, 48, 48, 48, 51]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 49, 54]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let effectiveTime ← readOptional [49, 54, 56] tokens
  let noTradingSessions ← readRequired [51, 56, 54] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let participationRate ← readOptional [56, 52, 57] tokens
  let locateBroker ← readOptional [53, 55, 48, 48] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let offsetPrice ← readOptional [57, 52, 48, 51] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let displayedLiquidityIndicator ← readOptional [57, 52, 50, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let parentFirmClOrdID ← readRequired [57, 52, 53, 49] tokens
  let interestType ← readOptional [57, 52, 55, 56] tokens
  let dealID ← readOptional [57, 52, 56, 51] tokens
  let dOrderAuctionPrice ← readOptional [57, 53, 54, 53] tokens
  let liquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let attributedQuote ← readOptional [50, 48, 48, 48, 49] tokens
  let proactiveIfLocked ← readOptional [50, 48, 48, 48, 50] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let workingPrice ← readOptional [50, 48, 48, 48, 52] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let workingAwayFromDisplay ← readOptional [50, 48, 48, 48, 54] tokens
  let unsolicitedAckType ← readOptional [50, 48, 48, 48, 55] tokens
  let participantType ← readOptional [50, 48, 48, 48, 56] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  let cATIMID ← readOptional [50, 48, 48, 52, 50] tokens
  let targetStrategy ← readOptional [50, 48, 48, 52, 54] tokens
  let f10b18 ← readOptional [50, 48, 48, 52, 55] tokens
  let auctionEligible ← readOptional [50, 48, 48, 52, 56] tokens
  let minParticpationRate ← readOptional [50, 48, 48, 52, 57] tokens
  let maxParticipationRate ← readOptional [50, 48, 48, 53, 48] tokens
  let wouldPrice ← readOptional [50, 48, 48, 53, 49] tokens
  let allocationFirmIntroducingBadgeID ← readOptional [50, 48, 48, 50, 52] tokens
  let allocationFirmMPID ← readOptional [50, 48, 48, 50, 50] tokens
  let refDealID ← readRequired [51, 48, 48, 48, 50] tokens
  let allocationIndicator ← readOptional [51, 48, 48, 48, 51] tokens
  let originalDealID ← readOptional [51, 48, 48, 48, 54] tokens
  let refExecTimestamp ← readOptional [51, 48, 48, 49, 54] tokens
  pure { account, clOrdID, cumQty, execID, execInst, execRefID, execTransType, lastMkt, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, symbolSfx, clientID, minQty, maxFloor, locateReqd, expireTime, execType, leavesQty, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, displayedLiquidityIndicator, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dealID, dOrderAuctionPrice, liquidityIndicator, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, workingPrice, flowIndicator, workingAwayFromDisplay, unsolicitedAckType, participantType, nanosecondSendingTime, nanosecondTransactTime, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice, allocationFirmIntroducingBadgeID, allocationFirmMPID, refDealID, allocationIndicator, originalDealID, refExecTimestamp }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have noTradingSessions := readRequired_part [51, 56, 54] record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have participationRate := readOptional_part [56, 52, 57] record.participationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have offsetPrice := readOptional_part [57, 52, 48, 51] record.offsetPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have displayedLiquidityIndicator := readOptional_part [57, 52, 50, 54] record.displayedLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have parentFirmClOrdID := readRequired_part [57, 52, 53, 49] record.parentFirmClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have interestType := readOptional_part [57, 52, 55, 56] record.interestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have dealID := readOptional_part [57, 52, 56, 51] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have dOrderAuctionPrice := readOptional_part [57, 53, 54, 53] record.dOrderAuctionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have liquidityIndicator := readOptional_part [57, 55, 51, 48] record.liquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have attributedQuote := readOptional_part [50, 48, 48, 48, 49] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have proactiveIfLocked := readOptional_part [50, 48, 48, 48, 50] record.proactiveIfLocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have workingPrice := readOptional_part [50, 48, 48, 48, 52] record.workingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have workingAwayFromDisplay := readOptional_part [50, 48, 48, 48, 54] record.workingAwayFromDisplay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have unsolicitedAckType := readOptional_part [50, 48, 48, 48, 55] record.unsolicitedAckType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have participantType := readOptional_part [50, 48, 48, 48, 56] record.participantType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have cATIMID := readOptional_part [50, 48, 48, 52, 50] record.cATIMID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have targetStrategy := readOptional_part [50, 48, 48, 52, 54] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have f10b18 := readOptional_part [50, 48, 48, 52, 55] record.f10b18 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have auctionEligible := readOptional_part [50, 48, 48, 52, 56] record.auctionEligible tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have minParticpationRate := readOptional_part [50, 48, 48, 52, 57] record.minParticpationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have maxParticipationRate := readOptional_part [50, 48, 48, 53, 48] record.maxParticipationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have wouldPrice := readOptional_part [50, 48, 48, 53, 49] record.wouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have allocationFirmIntroducingBadgeID := readOptional_part [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have allocationFirmMPID := readOptional_part [50, 48, 48, 50, 50] record.allocationFirmMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have refDealID := readRequired_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have allocationIndicator := readOptional_part [51, 48, 48, 48, 51] record.allocationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have originalDealID := readOptional_part [51, 48, 48, 48, 54] record.originalDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have refExecTimestamp := readOptional_part [51, 48, 48, 49, 54] record.refExecTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, clOrdID, cumQty, execID, execInst, execRefID, execTransType, lastMkt, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, symbolSfx, clientID, minQty, maxFloor, locateReqd, expireTime, execType, leavesQty, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, displayedLiquidityIndicator, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dealID, dOrderAuctionPrice, liquidityIndicator, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, workingPrice, flowIndicator, workingAwayFromDisplay, unsolicitedAckType, participantType, nanosecondSendingTime, nanosecondTransactTime, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice, allocationFirmIntroducingBadgeID, allocationFirmMPID, refDealID, allocationIndicator, originalDealID, refExecTimestamp, some_bind] <;> rfl

structure OrderCancelReject where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  cxlRejResponseTo : Terminated 1  -- tag 434
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[54, 48]], [[52, 51, 52]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  pure { clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejResponseTo, nanosecondSendingTime, nanosecondTransactTime }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejResponseTo, nanosecondSendingTime, nanosecondTransactTime, some_bind] <;> rfl

inductive Message where
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)

def Message.tokens : Message → List Token
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
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

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0

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

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NyseNyseequitiesFloorbrokerFixV26Exchange
