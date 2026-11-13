import Wire

/-!
# Chicago Board Options Exchange Drop Copy v2.8

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeEdgxoptionsDropcopyFixV28

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompId : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  deliverToCompId : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 53] record.onBehalfOfCompId,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 56] record.deliverToCompId,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[53, 50]], [[49, 50, 50]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let onBehalfOfCompId ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompId ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompId := readOptional_part [49, 49, 53] record.onBehalfOfCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompId := readOptional_part [49, 50, 56] record.deliverToCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID, some_bind] <;> rfl

structure ExecutionReport where
  execTransType : Option (Terminated 1)  -- tag 20
  multilegReportingType : Option (Terminated 1)  -- tag 442
  execID : Option (Terminated 1)  -- tag 17
  secondaryExecID : Option (Terminated 1)  -- tag 527
  execInst : Option (Terminated 1)  -- tag 18
  clOrdID : Option (Terminated 1)  -- tag 11
  tradeDate : Option (Terminated 1)  -- tag 75
  orderId : Option (Terminated 1)  -- tag 37
  ordStatus : Option (Terminated 1)  -- tag 39
  number : Option (Terminated 1)  -- tag 534
  affectedOrigClOrdID : Option (Terminated 1)  -- tag 1824
  crossID : Option (Terminated 1)  -- tag 548
  crossType : Option (Terminated 1)  -- tag 549
  crossPrioritization : Option (Terminated 1)  -- tag 550
  legRefID : Option (Terminated 1)  -- tag 654
  account : Option (Terminated 1)  -- tag 1
  symbol : Option (Terminated 1)  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  orderOrigin : Option (Terminated 1)  -- tag 9465
  held : Option (Terminated 1)  -- tag 20012
  frequentTraderID : Option (Terminated 1)  -- tag 21097
  strategyID : Option (Terminated 1)  -- tag 22002
  oRS : Option (Terminated 1)  -- tag 22003
  comboOrder : Option (Terminated 1)  -- tag 22005
  compression : Option (Terminated 1)  -- tag 22006
  openClose : Option (Terminated 1)  -- tag 77
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  maxFloor : Option (Terminated 1)  -- tag 111
  price : Option (Terminated 1)  -- tag 44
  displayRange : Option (Terminated 1)  -- tag 8020
  timeInForce : Option (Terminated 1)  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  sessionEligibility : Option (Terminated 1)  -- tag 22017
  expireTime : Option (Terminated 1)  -- tag 126
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  dayOrderQty : Option (Terminated 1)  -- tag 424
  cumQty : Option (Terminated 1)  -- tag 14
  dayCumQty : Option (Terminated 1)  -- tag 425
  lastShares : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  leavesQty : Option (Terminated 1)  -- tag 151
  avgPx : Option (Terminated 1)  -- tag 6
  for_ : Option (Terminated 1)  -- tag 426
  stopPx : Option (Terminated 1)  -- tag 99
  contraCapacity : Option (Terminated 1)  -- tag 7694
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  feeCode : Option (Terminated 1)  -- tag 9882
  marketingFeeCode : Option (Terminated 1)  -- tag 5937
  workingPrice : Option (Terminated 1)  -- tag 9690
  initialDisplayPrice : Option (Terminated 1)  -- tag 9691
  modifySequence : Option (Terminated 1)  -- tag 9617
  origCompID : Option (Terminated 1)  -- tag 9688
  origSubID : Option (Terminated 1)  -- tag 9689
  clearingSymbol : Option (Terminated 1)  -- tag 21053
  value : Option (Terminated 1)  -- tag 21050
  transactTime : Option (Terminated 1)  -- tag 60
  targetPartyID : Option (Terminated 1)  -- tag 1462
  text : Option (Terminated 1)  -- tag 58
  subreasonText : Option (Terminated 1)  -- tag 22058
  auctionID : Option (Terminated 1)  -- tag 9370
  crossExclusionIndicator : Option (Terminated 1)  -- tag 6438
  routing : Option (Terminated 1)  -- tag 7933
  drillThruProtection : Option (Terminated 1)  -- tag 6253
  clearingOptionalData : Option (Terminated 1)  -- tag 9324
  tradeThroughAlertType : Option (Terminated 1)  -- tag 21098
  floor : Option (Terminated 1)  -- tag 22049
  senderLocationID : Option (Terminated 1)  -- tag 142
  priceType : Option (Terminated 1)  -- tag 423
  initialClientOrderId : Option (Terminated 1)  -- tag 22020
  terminalOperatorId : Option (Terminated 1)  -- tag 22021
  additionalClientInfo : Option (Terminated 1)  -- tag 22022
  delta : Option (Terminated 1)  -- tag 22023
  legDelta : Option (Terminated 1)  -- tag 22024
  referencePrice : Option (Terminated 1)  -- tag 22025
  floorDestination : Option (Terminated 1)  -- tag 22100
  floorTradeTime : Option (Terminated 1)  -- tag 5179
  equityExDestination : Option (Terminated 1)  -- tag 22016
  occId : Option (Terminated 1)  -- tag 25019

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [50, 48] record.execTransType,
   Part.optional [52, 52, 50] record.multilegReportingType,
   Part.optional [49, 55] record.execID,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [51, 55] record.orderId,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [53, 51, 52] record.number,
   Part.optional [49, 56, 50, 52] record.affectedOrigClOrdID,
   Part.optional [53, 52, 56] record.crossID,
   Part.optional [53, 52, 57] record.crossType,
   Part.optional [53, 53, 48] record.crossPrioritization,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [49] record.account,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [57, 52, 54, 53] record.orderOrigin,
   Part.optional [50, 48, 48, 49, 50] record.held,
   Part.optional [50, 49, 48, 57, 55] record.frequentTraderID,
   Part.optional [50, 50, 48, 48, 50] record.strategyID,
   Part.optional [50, 50, 48, 48, 51] record.oRS,
   Part.optional [50, 50, 48, 48, 53] record.comboOrder,
   Part.optional [50, 50, 48, 48, 54] record.compression,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [52, 52] record.price,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 50, 48, 49, 55] record.sessionEligibility,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [52, 50, 52] record.dayOrderQty,
   Part.optional [49, 52] record.cumQty,
   Part.optional [52, 50, 53] record.dayCumQty,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 49] record.lastPx,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [54] record.avgPx,
   Part.optional [52, 50, 54] record.for_,
   Part.optional [57, 57] record.stopPx,
   Part.optional [55, 54, 57, 52] record.contraCapacity,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [57, 56, 56, 50] record.feeCode,
   Part.optional [53, 57, 51, 55] record.marketingFeeCode,
   Part.optional [57, 54, 57, 48] record.workingPrice,
   Part.optional [57, 54, 57, 49] record.initialDisplayPrice,
   Part.optional [57, 54, 49, 55] record.modifySequence,
   Part.optional [57, 54, 56, 56] record.origCompID,
   Part.optional [57, 54, 56, 57] record.origSubID,
   Part.optional [50, 49, 48, 53, 51] record.clearingSymbol,
   Part.optional [50, 49, 48, 53, 48] record.value,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 52, 54, 50] record.targetPartyID,
   Part.optional [53, 56] record.text,
   Part.optional [50, 50, 48, 53, 56] record.subreasonText,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [54, 52, 51, 56] record.crossExclusionIndicator,
   Part.optional [55, 57, 51, 51] record.routing,
   Part.optional [54, 50, 53, 51] record.drillThruProtection,
   Part.optional [57, 51, 50, 52] record.clearingOptionalData,
   Part.optional [50, 49, 48, 57, 56] record.tradeThroughAlertType,
   Part.optional [50, 50, 48, 52, 57] record.floor,
   Part.optional [49, 52, 50] record.senderLocationID,
   Part.optional [52, 50, 51] record.priceType,
   Part.optional [50, 50, 48, 50, 48] record.initialClientOrderId,
   Part.optional [50, 50, 48, 50, 49] record.terminalOperatorId,
   Part.optional [50, 50, 48, 50, 50] record.additionalClientInfo,
   Part.optional [50, 50, 48, 50, 51] record.delta,
   Part.optional [50, 50, 48, 50, 52] record.legDelta,
   Part.optional [50, 50, 48, 50, 53] record.referencePrice,
   Part.optional [50, 50, 49, 48, 48] record.floorDestination,
   Part.optional [53, 49, 55, 57] record.floorTradeTime,
   Part.optional [50, 50, 48, 49, 54] record.equityExDestination,
   Part.optional [50, 53, 48, 49, 57] record.occId]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[50, 48]], [[52, 52, 50]], [[49, 55]], [[53, 50, 55]], [[49, 56]], [[49, 49]], [[55, 53]], [[51, 55]], [[51, 57]], [[53, 51, 52]], [[49, 56, 50, 52]], [[53, 52, 56]], [[53, 52, 57]], [[53, 53, 48]], [[54, 53, 52]], [[49]], [[53, 53]], [[49, 54, 55]], [[57, 52, 54, 53]], [[50, 48, 48, 49, 50]], [[50, 49, 48, 57, 55]], [[50, 50, 48, 48, 50]], [[50, 50, 48, 48, 51]], [[50, 50, 48, 48, 53]], [[50, 50, 48, 48, 54]], [[55, 55]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[51, 56]], [[49, 49, 49]], [[52, 52]], [[56, 48, 50, 48]], [[53, 57]], [[52, 55]], [[50, 50, 48, 49, 55]], [[49, 50, 54]], [[52, 51, 57]], [[52, 52, 48]], [[52, 50, 52]], [[49, 52]], [[52, 50, 53]], [[51, 50]], [[51, 49]], [[49, 53, 49]], [[54]], [[52, 50, 54]], [[57, 57]], [[55, 54, 57, 52]], [[57, 55, 51, 48]], [[57, 56, 56, 50]], [[53, 57, 51, 55]], [[57, 54, 57, 48]], [[57, 54, 57, 49]], [[57, 54, 49, 55]], [[57, 54, 56, 56]], [[57, 54, 56, 57]], [[50, 49, 48, 53, 51]], [[50, 49, 48, 53, 48]], [[54, 48]], [[49, 52, 54, 50]], [[53, 56]], [[50, 50, 48, 53, 56]], [[57, 51, 55, 48]], [[54, 52, 51, 56]], [[55, 57, 51, 51]], [[54, 50, 53, 51]], [[57, 51, 50, 52]], [[50, 49, 48, 57, 56]], [[50, 50, 48, 52, 57]], [[49, 52, 50]], [[52, 50, 51]], [[50, 50, 48, 50, 48]], [[50, 50, 48, 50, 49]], [[50, 50, 48, 50, 50]], [[50, 50, 48, 50, 51]], [[50, 50, 48, 50, 52]], [[50, 50, 48, 50, 53]], [[50, 50, 49, 48, 48]], [[53, 49, 55, 57]], [[50, 50, 48, 49, 54]], [[50, 53, 48, 49, 57]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let execTransType ← readOptional [50, 48] tokens
  let multilegReportingType ← readOptional [52, 52, 50] tokens
  let execID ← readOptional [49, 55] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let orderId ← readOptional [51, 55] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let number ← readOptional [53, 51, 52] tokens
  let affectedOrigClOrdID ← readOptional [49, 56, 50, 52] tokens
  let crossID ← readOptional [53, 52, 56] tokens
  let crossType ← readOptional [53, 52, 57] tokens
  let crossPrioritization ← readOptional [53, 53, 48] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let account ← readOptional [49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let orderOrigin ← readOptional [57, 52, 54, 53] tokens
  let held ← readOptional [50, 48, 48, 49, 50] tokens
  let frequentTraderID ← readOptional [50, 49, 48, 57, 55] tokens
  let strategyID ← readOptional [50, 50, 48, 48, 50] tokens
  let oRS ← readOptional [50, 50, 48, 48, 51] tokens
  let comboOrder ← readOptional [50, 50, 48, 48, 53] tokens
  let compression ← readOptional [50, 50, 48, 48, 54] tokens
  let openClose ← readOptional [55, 55] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let price ← readOptional [52, 52] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let sessionEligibility ← readOptional [50, 50, 48, 49, 55] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let dayOrderQty ← readOptional [52, 50, 52] tokens
  let cumQty ← readOptional [49, 52] tokens
  let dayCumQty ← readOptional [52, 50, 53] tokens
  let lastShares ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let avgPx ← readOptional [54] tokens
  let for_ ← readOptional [52, 50, 54] tokens
  let stopPx ← readOptional [57, 57] tokens
  let contraCapacity ← readOptional [55, 54, 57, 52] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  let marketingFeeCode ← readOptional [53, 57, 51, 55] tokens
  let workingPrice ← readOptional [57, 54, 57, 48] tokens
  let initialDisplayPrice ← readOptional [57, 54, 57, 49] tokens
  let modifySequence ← readOptional [57, 54, 49, 55] tokens
  let origCompID ← readOptional [57, 54, 56, 56] tokens
  let origSubID ← readOptional [57, 54, 56, 57] tokens
  let clearingSymbol ← readOptional [50, 49, 48, 53, 51] tokens
  let value ← readOptional [50, 49, 48, 53, 48] tokens
  let transactTime ← readOptional [54, 48] tokens
  let targetPartyID ← readOptional [49, 52, 54, 50] tokens
  let text ← readOptional [53, 56] tokens
  let subreasonText ← readOptional [50, 50, 48, 53, 56] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let crossExclusionIndicator ← readOptional [54, 52, 51, 56] tokens
  let routing ← readOptional [55, 57, 51, 51] tokens
  let drillThruProtection ← readOptional [54, 50, 53, 51] tokens
  let clearingOptionalData ← readOptional [57, 51, 50, 52] tokens
  let tradeThroughAlertType ← readOptional [50, 49, 48, 57, 56] tokens
  let floor ← readOptional [50, 50, 48, 52, 57] tokens
  let senderLocationID ← readOptional [49, 52, 50] tokens
  let priceType ← readOptional [52, 50, 51] tokens
  let initialClientOrderId ← readOptional [50, 50, 48, 50, 48] tokens
  let terminalOperatorId ← readOptional [50, 50, 48, 50, 49] tokens
  let additionalClientInfo ← readOptional [50, 50, 48, 50, 50] tokens
  let delta ← readOptional [50, 50, 48, 50, 51] tokens
  let legDelta ← readOptional [50, 50, 48, 50, 52] tokens
  let referencePrice ← readOptional [50, 50, 48, 50, 53] tokens
  let floorDestination ← readOptional [50, 50, 49, 48, 48] tokens
  let floorTradeTime ← readOptional [53, 49, 55, 57] tokens
  let equityExDestination ← readOptional [50, 50, 48, 49, 54] tokens
  let occId ← readOptional [50, 53, 48, 49, 57] tokens
  pure { execTransType, multilegReportingType, execID, secondaryExecID, execInst, clOrdID, tradeDate, orderId, ordStatus, number, affectedOrigClOrdID, crossID, crossType, crossPrioritization, legRefID, account, symbol, securityType, orderOrigin, held, frequentTraderID, strategyID, oRS, comboOrder, compression, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, side, orderQty, maxFloor, price, displayRange, timeInForce, rule80A, sessionEligibility, expireTime, clearingFirm, clearingAccount, dayOrderQty, cumQty, dayCumQty, lastShares, lastPx, leavesQty, avgPx, for_, stopPx, contraCapacity, tradeLiquidityIndicator, feeCode, marketingFeeCode, workingPrice, initialDisplayPrice, modifySequence, origCompID, origSubID, clearingSymbol, value, transactTime, targetPartyID, text, subreasonText, auctionID, crossExclusionIndicator, routing, drillThruProtection, clearingOptionalData, tradeThroughAlertType, floor, senderLocationID, priceType, initialClientOrderId, terminalOperatorId, additionalClientInfo, delta, legDelta, referencePrice, floorDestination, floorTradeTime, equityExDestination, occId }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have multilegReportingType := readOptional_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have number := readOptional_part [53, 51, 52] record.number tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have affectedOrigClOrdID := readOptional_part [49, 56, 50, 52] record.affectedOrigClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have crossID := readOptional_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have crossType := readOptional_part [53, 52, 57] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have crossPrioritization := readOptional_part [53, 53, 48] record.crossPrioritization tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have orderOrigin := readOptional_part [57, 52, 54, 53] record.orderOrigin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have held := readOptional_part [50, 48, 48, 49, 50] record.held tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have frequentTraderID := readOptional_part [50, 49, 48, 57, 55] record.frequentTraderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have strategyID := readOptional_part [50, 50, 48, 48, 50] record.strategyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have oRS := readOptional_part [50, 50, 48, 48, 51] record.oRS tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have comboOrder := readOptional_part [50, 50, 48, 48, 53] record.comboOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have compression := readOptional_part [50, 50, 48, 48, 54] record.compression tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have sessionEligibility := readOptional_part [50, 50, 48, 49, 55] record.sessionEligibility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have dayOrderQty := readOptional_part [52, 50, 52] record.dayOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have dayCumQty := readOptional_part [52, 50, 53] record.dayCumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have for_ := readOptional_part [52, 50, 54] record.for_ tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have contraCapacity := readOptional_part [55, 54, 57, 52] record.contraCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have marketingFeeCode := readOptional_part [53, 57, 51, 55] record.marketingFeeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have workingPrice := readOptional_part [57, 54, 57, 48] record.workingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have initialDisplayPrice := readOptional_part [57, 54, 57, 49] record.initialDisplayPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have modifySequence := readOptional_part [57, 54, 49, 55] record.modifySequence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have origCompID := readOptional_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have origSubID := readOptional_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have clearingSymbol := readOptional_part [50, 49, 48, 53, 51] record.clearingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have value := readOptional_part [50, 49, 48, 53, 48] record.value tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have targetPartyID := readOptional_part [49, 52, 54, 50] record.targetPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have subreasonText := readOptional_part [50, 50, 48, 53, 56] record.subreasonText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have crossExclusionIndicator := readOptional_part [54, 52, 51, 56] record.crossExclusionIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have routing := readOptional_part [55, 57, 51, 51] record.routing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have drillThruProtection := readOptional_part [54, 50, 53, 51] record.drillThruProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have clearingOptionalData := readOptional_part [57, 51, 50, 52] record.clearingOptionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have tradeThroughAlertType := readOptional_part [50, 49, 48, 57, 56] record.tradeThroughAlertType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have floor := readOptional_part [50, 50, 48, 52, 57] record.floor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  have senderLocationID := readOptional_part [49, 52, 50] record.senderLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 72 (by decide +kernel)))
  have priceType := readOptional_part [52, 50, 51] record.priceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 73 (by decide +kernel)))
  have initialClientOrderId := readOptional_part [50, 50, 48, 50, 48] record.initialClientOrderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 74 (by decide +kernel)))
  have terminalOperatorId := readOptional_part [50, 50, 48, 50, 49] record.terminalOperatorId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 75 (by decide +kernel)))
  have additionalClientInfo := readOptional_part [50, 50, 48, 50, 50] record.additionalClientInfo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 76 (by decide +kernel)))
  have delta := readOptional_part [50, 50, 48, 50, 51] record.delta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 77 (by decide +kernel)))
  have legDelta := readOptional_part [50, 50, 48, 50, 52] record.legDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 78 (by decide +kernel)))
  have referencePrice := readOptional_part [50, 50, 48, 50, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 79 (by decide +kernel)))
  have floorDestination := readOptional_part [50, 50, 49, 48, 48] record.floorDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 80 (by decide +kernel)))
  have floorTradeTime := readOptional_part [53, 49, 55, 57] record.floorTradeTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 81 (by decide +kernel)))
  have equityExDestination := readOptional_part [50, 50, 48, 49, 54] record.equityExDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 82 (by decide +kernel)))
  have occId := readOptional_part [50, 53, 48, 49, 57] record.occId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 83 (by decide +kernel)))
  simp only [ExecutionReport.decode, execTransType, multilegReportingType, execID, secondaryExecID, execInst, clOrdID, tradeDate, orderId, ordStatus, number, affectedOrigClOrdID, crossID, crossType, crossPrioritization, legRefID, account, symbol, securityType, orderOrigin, held, frequentTraderID, strategyID, oRS, comboOrder, compression, openClose, maturityMonth, maturityDay, putOrCall, strikePrice, side, orderQty, maxFloor, price, displayRange, timeInForce, rule80A, sessionEligibility, expireTime, clearingFirm, clearingAccount, dayOrderQty, cumQty, dayCumQty, lastShares, lastPx, leavesQty, avgPx, for_, stopPx, contraCapacity, tradeLiquidityIndicator, feeCode, marketingFeeCode, workingPrice, initialDisplayPrice, modifySequence, origCompID, origSubID, clearingSymbol, value, transactTime, targetPartyID, text, subreasonText, auctionID, crossExclusionIndicator, routing, drillThruProtection, clearingOptionalData, tradeThroughAlertType, floor, senderLocationID, priceType, initialClientOrderId, terminalOperatorId, additionalClientInfo, delta, legDelta, referencePrice, floorDestination, floorTradeTime, equityExDestination, occId, some_bind] <;> rfl

structure ExecutionReportNew

def ExecutionReportNew.parts (_ : ExecutionReportNew) : List Part :=
  []

def ExecutionReportNew.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportNew.shape (record : ExecutionReportNew) : record.parts.map Part.tags = ExecutionReportNew.tags := rfl

def ExecutionReportNew.decode (_ : List Token) : Option ExecutionReportNew := some {}

theorem ExecutionReportNew.decode_agrees (record : ExecutionReportNew) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNew.decode tokens = some record := by
  rfl

structure ExecutionReportPartialFill where
  noContraBrokers : Option (Terminated 1)  -- tag 382
  contraBroker : Option (Terminated 1)  -- tag 375
  contraTrader : Option (Terminated 1)  -- tag 337

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 51, 55] record.contraTrader]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[51, 56, 50]], [[51, 55, 53]], [[51, 51, 55]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let contraTrader ← readOptional [51, 51, 55] tokens
  pure { noContraBrokers, contraBroker, contraTrader }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraTrader := readOptional_part [51, 51, 55] record.contraTrader tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, noContraBrokers, contraBroker, contraTrader, some_bind] <;> rfl

structure ExecutionReportFill where
  noContraBrokers : Option (Terminated 1)  -- tag 382
  contraBroker : Option (Terminated 1)  -- tag 375
  contraTrader : Option (Terminated 1)  -- tag 337

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 51, 55] record.contraTrader]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[51, 56, 50]], [[51, 55, 53]], [[51, 51, 55]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let contraTrader ← readOptional [51, 51, 55] tokens
  pure { noContraBrokers, contraBroker, contraTrader }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraTrader := readOptional_part [51, 51, 55] record.contraTrader tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, noContraBrokers, contraBroker, contraTrader, some_bind] <;> rfl

structure ExecutionReportDoneForDay

def ExecutionReportDoneForDay.parts (_ : ExecutionReportDoneForDay) : List Part :=
  []

def ExecutionReportDoneForDay.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportDoneForDay.shape (record : ExecutionReportDoneForDay) : record.parts.map Part.tags = ExecutionReportDoneForDay.tags := rfl

def ExecutionReportDoneForDay.decode (_ : List Token) : Option ExecutionReportDoneForDay := some {}

theorem ExecutionReportDoneForDay.decode_agrees (record : ExecutionReportDoneForDay) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportDoneForDay.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportDoneForDay.decode tokens = some record := by
  rfl

structure ExecutionReportCanceled where
  origClOrdID : Option (Terminated 1)  -- tag 41
  secondaryOrderID : Option (Terminated 1)  -- tag 198

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 57, 56] record.secondaryOrderID]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 57, 56]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let origClOrdID ← readOptional [52, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  pure { origClOrdID, secondaryOrderID }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, origClOrdID, secondaryOrderID, some_bind] <;> rfl

structure ExecutionReportReplaced where
  origClOrdID : Option (Terminated 1)  -- tag 41

def ExecutionReportReplaced.parts (record : ExecutionReportReplaced) : List Part :=
  [Part.optional [52, 49] record.origClOrdID]

def ExecutionReportReplaced.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem ExecutionReportReplaced.shape (record : ExecutionReportReplaced) : record.parts.map Part.tags = ExecutionReportReplaced.tags := rfl

def ExecutionReportReplaced.decode (tokens : List Token) : Option ExecutionReportReplaced := do
  let origClOrdID ← readOptional [52, 49] tokens
  pure { origClOrdID }

theorem ExecutionReportReplaced.decode_agrees (record : ExecutionReportReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplaced.decode tokens = some record := by
  have distinct : ExecutionReportReplaced.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportReplaced.decode, origClOrdID, some_bind] <;> rfl

structure ExecutionReportRejected where
  ordRejReason : Option (Terminated 1)  -- tag 103

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [49, 48, 51] record.ordRejReason]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[49, 48, 51]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let ordRejReason ← readOptional [49, 48, 51] tokens
  pure { ordRejReason }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, ordRejReason, some_bind] <;> rfl

structure ExecutionReportRestated where
  execRestatementReason : Option (Terminated 1)  -- tag 378
  execRefID : Option (Terminated 1)  -- tag 19
  secondaryOrderID : Option (Terminated 1)  -- tag 198

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [49, 57] record.execRefID,
   Part.optional [49, 57, 56] record.secondaryOrderID]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]], [[49, 57]], [[49, 57, 56]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let execRefID ← readOptional [49, 57] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  pure { execRestatementReason, execRefID, secondaryOrderID }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, execRestatementReason, execRefID, secondaryOrderID, some_bind] <;> rfl

structure ExecutionReportMassCancelComplete where
  massCancelID : Option (Terminated 1)  -- tag 7695
  cancelledOrderCount : Option (Terminated 1)  -- tag 7696
  matchingUnit : Option (Terminated 1)  -- tag 25017

def ExecutionReportMassCancelComplete.parts (record : ExecutionReportMassCancelComplete) : List Part :=
  [Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.optional [55, 54, 57, 54] record.cancelledOrderCount,
   Part.optional [50, 53, 48, 49, 55] record.matchingUnit]

def ExecutionReportMassCancelComplete.tags : List (List (List UInt8)) :=
  [[[55, 54, 57, 53]], [[55, 54, 57, 54]], [[50, 53, 48, 49, 55]]]

theorem ExecutionReportMassCancelComplete.shape (record : ExecutionReportMassCancelComplete) : record.parts.map Part.tags = ExecutionReportMassCancelComplete.tags := rfl

def ExecutionReportMassCancelComplete.decode (tokens : List Token) : Option ExecutionReportMassCancelComplete := do
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let cancelledOrderCount ← readOptional [55, 54, 57, 54] tokens
  let matchingUnit ← readOptional [50, 53, 48, 49, 55] tokens
  pure { massCancelID, cancelledOrderCount, matchingUnit }

theorem ExecutionReportMassCancelComplete.decode_agrees (record : ExecutionReportMassCancelComplete) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportMassCancelComplete.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportMassCancelComplete.decode tokens = some record := by
  have distinct : ExecutionReportMassCancelComplete.tags.flatten.Nodup := by decide +kernel
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have cancelledOrderCount := readOptional_part [55, 54, 57, 54] record.cancelledOrderCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have matchingUnit := readOptional_part [50, 53, 48, 49, 55] record.matchingUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportMassCancelComplete.decode, massCancelID, cancelledOrderCount, matchingUnit, some_bind] <;> rfl

structure ExecutionReportPurgeNotification where
  massCancelID : Option (Terminated 1)  -- tag 7695

def ExecutionReportPurgeNotification.parts (record : ExecutionReportPurgeNotification) : List Part :=
  [Part.optional [55, 54, 57, 53] record.massCancelID]

def ExecutionReportPurgeNotification.tags : List (List (List UInt8)) :=
  [[[55, 54, 57, 53]]]

theorem ExecutionReportPurgeNotification.shape (record : ExecutionReportPurgeNotification) : record.parts.map Part.tags = ExecutionReportPurgeNotification.tags := rfl

def ExecutionReportPurgeNotification.decode (tokens : List Token) : Option ExecutionReportPurgeNotification := do
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  pure { massCancelID }

theorem ExecutionReportPurgeNotification.decode_agrees (record : ExecutionReportPurgeNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPurgeNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPurgeNotification.decode tokens = some record := by
  have distinct : ExecutionReportPurgeNotification.tags.flatten.Nodup := by decide +kernel
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportPurgeNotification.decode, massCancelID, some_bind] <;> rfl

structure TradeCancelCorrectFIXDropClearingEdit where
  execTransType : Option (Terminated 1)  -- tag 20
  execID : Option (Terminated 1)  -- tag 17
  number : Option (Terminated 1)  -- tag 534
  listSeqNo : Option (Terminated 1)  -- tag 67
  waveNo : Option (Terminated 1)  -- tag 105
  allocID : Option (Terminated 1)  -- tag 70
  allocExecRefID : Option (Terminated 1)  -- tag 25007
  contracts : Option (Terminated 1)  -- tag 80
  openClose : Option (Terminated 1)  -- tag 77
  allocClearingFirm : Option (Terminated 1)  -- tag 25008
  account : Option (Terminated 1)  -- tag 1
  partyID : Option (Terminated 1)  -- tag 448
  partySubID : Option (Terminated 1)  -- tag 523
  clearingOptionalData : Option (Terminated 1)  -- tag 9324
  allocClOrdID : Option (Terminated 1)  -- tag 25009
  rule80A : Option (Terminated 1)  -- tag 47
  orderId : Option (Terminated 1)  -- tag 37
  symbol : Option (Terminated 1)  -- tag 55
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Option (Terminated 1)  -- tag 54
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  lastShares : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  origTime : Option (Terminated 1)  -- tag 42
  transactTime : Option (Terminated 1)  -- tag 60
  clearingAccount : Option (Terminated 1)  -- tag 440
  clearingFirm : Option (Terminated 1)  -- tag 439
  clOrdID : Option (Terminated 1)  -- tag 11
  execRefID : Option (Terminated 1)  -- tag 19

def TradeCancelCorrectFIXDropClearingEdit.parts (record : TradeCancelCorrectFIXDropClearingEdit) : List Part :=
  [Part.optional [50, 48] record.execTransType,
   Part.optional [49, 55] record.execID,
   Part.optional [53, 51, 52] record.number,
   Part.optional [54, 55] record.listSeqNo,
   Part.optional [49, 48, 53] record.waveNo,
   Part.optional [55, 48] record.allocID,
   Part.optional [50, 53, 48, 48, 55] record.allocExecRefID,
   Part.optional [56, 48] record.contracts,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 53, 48, 48, 56] record.allocClearingFirm,
   Part.optional [49] record.account,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [53, 50, 51] record.partySubID,
   Part.optional [57, 51, 50, 52] record.clearingOptionalData,
   Part.optional [50, 53, 48, 48, 57] record.allocClOrdID,
   Part.optional [52, 55] record.rule80A,
   Part.optional [51, 55] record.orderId,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 52] record.side,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 49] record.lastPx,
   Part.optional [52, 50] record.origTime,
   Part.optional [54, 48] record.transactTime,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 57] record.execRefID]

def TradeCancelCorrectFIXDropClearingEdit.tags : List (List (List UInt8)) :=
  [[[50, 48]], [[49, 55]], [[53, 51, 52]], [[54, 55]], [[49, 48, 53]], [[55, 48]], [[50, 53, 48, 48, 55]], [[56, 48]], [[55, 55]], [[50, 53, 48, 48, 56]], [[49]], [[52, 52, 56]], [[53, 50, 51]], [[57, 51, 50, 52]], [[50, 53, 48, 48, 57]], [[52, 55]], [[51, 55]], [[53, 53]], [[50, 48, 48]], [[50, 48, 53]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[57, 55, 51, 48]], [[51, 50]], [[51, 49]], [[52, 50]], [[54, 48]], [[52, 52, 48]], [[52, 51, 57]], [[49, 49]], [[49, 57]]]

theorem TradeCancelCorrectFIXDropClearingEdit.shape (record : TradeCancelCorrectFIXDropClearingEdit) : record.parts.map Part.tags = TradeCancelCorrectFIXDropClearingEdit.tags := rfl

def TradeCancelCorrectFIXDropClearingEdit.decode (tokens : List Token) : Option TradeCancelCorrectFIXDropClearingEdit := do
  let execTransType ← readOptional [50, 48] tokens
  let execID ← readOptional [49, 55] tokens
  let number ← readOptional [53, 51, 52] tokens
  let listSeqNo ← readOptional [54, 55] tokens
  let waveNo ← readOptional [49, 48, 53] tokens
  let allocID ← readOptional [55, 48] tokens
  let allocExecRefID ← readOptional [50, 53, 48, 48, 55] tokens
  let contracts ← readOptional [56, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let allocClearingFirm ← readOptional [50, 53, 48, 48, 56] tokens
  let account ← readOptional [49] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partySubID ← readOptional [53, 50, 51] tokens
  let clearingOptionalData ← readOptional [57, 51, 50, 52] tokens
  let allocClOrdID ← readOptional [50, 53, 48, 48, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let orderId ← readOptional [51, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readOptional [53, 52] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let lastShares ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let origTime ← readOptional [52, 50] tokens
  let transactTime ← readOptional [54, 48] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let execRefID ← readOptional [49, 57] tokens
  pure { execTransType, execID, number, listSeqNo, waveNo, allocID, allocExecRefID, contracts, openClose, allocClearingFirm, account, partyID, partySubID, clearingOptionalData, allocClOrdID, rule80A, orderId, symbol, maturityMonth, maturityDay, putOrCall, strikePrice, side, tradeLiquidityIndicator, lastShares, lastPx, origTime, transactTime, clearingAccount, clearingFirm, clOrdID, execRefID }

theorem TradeCancelCorrectFIXDropClearingEdit.decode_agrees (record : TradeCancelCorrectFIXDropClearingEdit) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCancelCorrectFIXDropClearingEdit.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCancelCorrectFIXDropClearingEdit.decode tokens = some record := by
  have distinct : TradeCancelCorrectFIXDropClearingEdit.tags.flatten.Nodup := by decide +kernel
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have number := readOptional_part [53, 51, 52] record.number tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have listSeqNo := readOptional_part [54, 55] record.listSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have waveNo := readOptional_part [49, 48, 53] record.waveNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have allocID := readOptional_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have allocExecRefID := readOptional_part [50, 53, 48, 48, 55] record.allocExecRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have contracts := readOptional_part [56, 48] record.contracts tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have allocClearingFirm := readOptional_part [50, 53, 48, 48, 56] record.allocClearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have partySubID := readOptional_part [53, 50, 51] record.partySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have clearingOptionalData := readOptional_part [57, 51, 50, 52] record.clearingOptionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have allocClOrdID := readOptional_part [50, 53, 48, 48, 57] record.allocClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have origTime := readOptional_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  simp only [TradeCancelCorrectFIXDropClearingEdit.decode, execTransType, execID, number, listSeqNo, waveNo, allocID, allocExecRefID, contracts, openClose, allocClearingFirm, account, partyID, partySubID, clearingOptionalData, allocClOrdID, rule80A, orderId, symbol, maturityMonth, maturityDay, putOrCall, strikePrice, side, tradeLiquidityIndicator, lastShares, lastPx, origTime, transactTime, clearingAccount, clearingFirm, clOrdID, execRefID, some_bind] <;> rfl

structure NoLegs where
  legRefID : Terminated 1  -- tag 654
  legSymbol : Terminated 1  -- tag 600
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  legPrice : Option (Terminated 1)  -- tag 566
  legPositionEffect : Terminated 1  -- tag 564
  legDelta : Option (Terminated 1)  -- tag 22024

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 53, 52] record.legRefID,
   Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [53, 54, 54] record.legPrice,
   Part.required [53, 54, 52] record.legPositionEffect,
   Part.optional [50, 50, 48, 50, 52] record.legDelta]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 53, 52]], [[54, 48, 48]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[53, 54, 54]], [[53, 54, 52]], [[50, 50, 48, 50, 52]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legRefID ← readRequired [54, 53, 52] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legPrice ← readOptional [53, 54, 54] tokens
  let legPositionEffect ← readRequired [53, 54, 52] tokens
  let legDelta ← readOptional [50, 50, 48, 50, 52] tokens
  pure { legRefID, legSymbol, legMaturityDate, legStrikePrice, legRatioQty, legSide, legPrice, legPositionEffect, legDelta }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legPrice := readOptional_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legPositionEffect := readRequired_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have legDelta := readOptional_part [50, 50, 48, 50, 52] record.legDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoLegs.decode, legRefID, legSymbol, legMaturityDate, legStrikePrice, legRatioQty, legSide, legPrice, legPositionEffect, legDelta, some_bind] <;> rfl

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

structure SecurityDefinition where
  clOrdID : Option (Terminated 1)  -- tag 11
  securityType : Option (Terminated 1)  -- tag 167
  account : Option (Terminated 1)  -- tag 1
  symbol : Option (Terminated 1)  -- tag 55
  securityResponseType : Option (Terminated 1)  -- tag 323
  noLegs : List NoLegs  -- tag 555
  noOfSecurities : Option (Terminated 1)  -- tag 8641
  text : Option (Terminated 1)  -- tag 58

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [49] record.account,
   Part.optional [53, 53] record.symbol,
   Part.optional [51, 50, 51] record.securityResponseType,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [56, 54, 52, 49] record.noOfSecurities,
   Part.optional [53, 56] record.text]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 54, 55]], [[49]], [[53, 53]], [[51, 50, 51]], [53, 53, 53] :: NoLegs.members, [[56, 54, 52, 49]], [[53, 56]]]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let clOrdID ← readOptional [49, 49] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let account ← readOptional [49] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityResponseType ← readOptional [51, 50, 51] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.decode tokens
  let noOfSecurities ← readOptional [56, 54, 52, 49] tokens
  let text ← readOptional [53, 56] tokens
  pure { clOrdID, securityType, account, symbol, securityResponseType, noLegs, noOfSecurities, text }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityResponseType := readOptional_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 53, 52] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noOfSecurities := readOptional_part [56, 54, 52, 49] record.noOfSecurities tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [SecurityDefinition.decode, clOrdID, securityType, account, symbol, securityResponseType, noLegs, noOfSecurities, text, some_bind] <;> rfl

inductive Message where
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportMassCancelComplete (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportMassCancelComplete)
  | executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification)
  | tradeCancelCorrectFIXDropClearingEdit (header : Header) (r0 : TradeCancelCorrectFIXDropClearingEdit)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)

def Message.tokens : Message → List Token
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportDoneForDay header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportMassCancelComplete header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts)
  | .executionReportPurgeNotification header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts)
  | .tradeCancelCorrectFIXDropClearingEdit header r0 => ⟨[51, 53], ⟨[85, 67, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], ⟨[100], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNew.decode rest
              pure (.executionReportNew header r0 r1)
            else none
          else if key.val = [49] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPartialFill.decode rest
              pure (.executionReportPartialFill header r0 r1)
            else none
          else if key.val = [50] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportFill.decode rest
              pure (.executionReportFill header r0 r1)
            else none
          else if key.val = [51] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportDoneForDay.decode rest
              pure (.executionReportDoneForDay header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCanceled.decode rest
              pure (.executionReportCanceled header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportReplaced.decode rest
              pure (.executionReportReplaced header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [68] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRestated.decode rest
              pure (.executionReportRestated header r0 r1)
            else none
          else if key.val = [77] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportMassCancelComplete.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportMassCancelComplete.decode rest
              pure (.executionReportMassCancelComplete header r0 r1)
            else none
          else if key.val = [80] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPurgeNotification.decode rest
              pure (.executionReportPurgeNotification header r0 r1)
            else none
          else none
      else if token.value.val = [85, 67, 67] then
        if known (Header.tags ++ TradeCancelCorrectFIXDropClearingEdit.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCancelCorrectFIXDropClearingEdit.decode rest
          pure (.tradeCancelCorrectFIXDropClearingEdit header r0)
        else none
      else if token.value.val = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else none
    else none

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, some_bind] <;> rfl

theorem Message.decode_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decode (Message.tokens (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPartialFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPartialFill.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPartialFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill) :
    Message.decode (Message.tokens (.executionReportFill header r0 r1)) = some (.executionReportFill header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportFill.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay) :
    Message.decode (Message.tokens (.executionReportDoneForDay header r0 r1)) = some (.executionReportDoneForDay header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[51], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportDoneForDay.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportDoneForDay.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportDoneForDay.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decode (Message.tokens (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCanceled.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCanceled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decode (Message.tokens (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportReplaced.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportReplaced.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportReplaced.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decode (Message.tokens (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejected.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decode (Message.tokens (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[68], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRestated.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRestated.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRestated.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportMassCancelComplete (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportMassCancelComplete) :
    Message.decode (Message.tokens (.executionReportMassCancelComplete header r0 r1)) = some (.executionReportMassCancelComplete header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportMassCancelComplete.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportMassCancelComplete.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[77], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[77], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportMassCancelComplete.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportMassCancelComplete.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportMassCancelComplete.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportMassCancelComplete.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification) :
    Message.decode (Message.tokens (.executionReportPurgeNotification header r0 r1)) = some (.executionReportPurgeNotification header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[80], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPurgeNotification.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPurgeNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCancelCorrectFIXDropClearingEdit (header : Header) (r0 : TradeCancelCorrectFIXDropClearingEdit) :
    Message.decode (Message.tokens (.tradeCancelCorrectFIXDropClearingEdit header r0)) = some (.tradeCancelCorrectFIXDropClearingEdit header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrectFIXDropClearingEdit.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCancelCorrectFIXDropClearingEdit.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrectFIXDropClearingEdit.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCancelCorrectFIXDropClearingEdit.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decode_executionReportDoneForDay header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportMassCancelComplete header r0 r1 => exact Message.decode_executionReportMassCancelComplete header r0 r1
  | executionReportPurgeNotification header r0 r1 => exact Message.decode_executionReportPurgeNotification header r0 r1
  | tradeCancelCorrectFIXDropClearingEdit header r0 => exact Message.decode_tradeCancelCorrectFIXDropClearingEdit header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decodeBytes (Message.encode (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPartialFill header r0 r1

theorem Message.decodeBytes_executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill) :
    Message.decodeBytes (Message.encode (.executionReportFill header r0 r1)) = some (.executionReportFill header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFill.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFill header r0 r1

theorem Message.decodeBytes_executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay) :
    Message.decodeBytes (Message.encode (.executionReportDoneForDay header r0 r1)) = some (.executionReportDoneForDay header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportDoneForDay.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportDoneForDay header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCanceled.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decodeBytes (Message.encode (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplaced.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplaced header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated) :
    Message.decodeBytes (Message.encode (.executionReportRestated header r0 r1)) = some (.executionReportRestated header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRestated.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRestated header r0 r1

theorem Message.decodeBytes_executionReportMassCancelComplete (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportMassCancelComplete) :
    Message.decodeBytes (Message.encode (.executionReportMassCancelComplete header r0 r1)) = some (.executionReportMassCancelComplete header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportMassCancelComplete.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportMassCancelComplete header r0 r1

theorem Message.decodeBytes_executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification) :
    Message.decodeBytes (Message.encode (.executionReportPurgeNotification header r0 r1)) = some (.executionReportPurgeNotification header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPurgeNotification header r0 r1

theorem Message.decodeBytes_tradeCancelCorrectFIXDropClearingEdit (header : Header) (r0 : TradeCancelCorrectFIXDropClearingEdit) :
    Message.decodeBytes (Message.encode (.tradeCancelCorrectFIXDropClearingEdit header r0)) = some (.tradeCancelCorrectFIXDropClearingEdit header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 67, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCancelCorrectFIXDropClearingEdit.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCancelCorrectFIXDropClearingEdit header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[100], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportDoneForDay header r0 r1 => exact Message.decodeBytes_executionReportDoneForDay header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportMassCancelComplete header r0 r1 => exact Message.decodeBytes_executionReportMassCancelComplete header r0 r1
  | executionReportPurgeNotification header r0 r1 => exact Message.decodeBytes_executionReportPurgeNotification header r0 r1
  | tradeCancelCorrectFIXDropClearingEdit header r0 => exact Message.decodeBytes_tradeCancelCorrectFIXDropClearingEdit header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeEdgxoptionsDropcopyFixV28
