import Wire

/-!
# Chicago Board Options Exchange Drop Copy v8.73

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBidsjapanDropcopyFixV873

structure Header where
  msgSeqNum : Option (Terminated 1)  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Option (Terminated 1)  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128

def Header.parts (record : Header) : List Part :=
  [Part.optional [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readOptional [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID }

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
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
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
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, some_bind] <;> rfl

structure ExecutionReport where
  account : Terminated 1  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execRefID : Option (Terminated 1)  -- tag 19
  execTransType : Terminated 1  -- tag 20
  iDSource : Option (Terminated 1)  -- tag 22
  lastMkt : Option (Terminated 1)  -- tag 30
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  rule80A : Terminated 1  -- tag 47
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Terminated 1  -- tag 76
  clientID : Terminated 1  -- tag 109
  minQty : Terminated 1  -- tag 110
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
  leavesQty : Terminated 1  -- tag 151
  effectiveTime : Terminated 1  -- tag 168
  securityExchange : Option (Terminated 1)  -- tag 207
  pegDifference : Option (Terminated 1)  -- tag 211
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  clearingFirm : Option (Terminated 1)  -- tag 439
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  orderCapacity : Terminated 1  -- tag 528
  trdRegTimestamp : Option (Terminated 1)  -- tag 769
  bookingType : Terminated 1  -- tag 775
  lastLiquidityInd : Option (Terminated 1)  -- tag 9730
  regulatoryTradeID : Option (Terminated 1)  -- tag 1903
  regulatoryTradeIDType : Option (Terminated 1)  -- tag 1906
  noRegulatoryTradeIDs : Option (Terminated 1)  -- tag 1907
  locateBroker : Option (Terminated 1)  -- tag 5700
  locateIdentifier : Option (Terminated 1)  -- tag 5701
  bIDSPriceProtection : Option (Terminated 1)  -- tag 8017
  tradingVenueRegulatoryTradeID : Option (Terminated 1)  -- tag 8016
  bIDSTradeId : Option (Terminated 1)  -- tag 8026
  bIDSReportingType : Terminated 1  -- tag 8052
  bIDSUniqueClOrdID : Option (Terminated 1)  -- tag 8063
  bIDSSponsoredTraderName : Option (Terminated 1)  -- tag 8067
  bIDSCentralCounterparty : Option (Terminated 1)  -- tag 8069
  targetContraFirm : Option (Terminated 1)  -- tag 8070
  bIDSAEFirm : Option (Terminated 1)  -- tag 8082
  bIDSAEVolume : Option (Terminated 1)  -- tag 8086
  bIDSAEBookingType : Option (Terminated 1)  -- tag 8088
  bIDSAEFilledVolume : Option (Terminated 1)  -- tag 8089
  partyIDOrderOriginationFirm : Option (Terminated 1)  -- tag 20013
  lEIOrderOrigination : Option (Terminated 1)  -- tag 1724
  lEIRoutingArrangementIndicator : Option (Terminated 1)  -- tag 2883
  uMIRRegulationID : Option (Terminated 1)  -- tag 6763
  principalTrade : Option (Terminated 1)  -- tag 6776
  washTradeIndicator : Option (Terminated 1)  -- tag 6777
  programTrade : Option (Terminated 1)  -- tag 7003
  anonymous : Option (Terminated 1)  -- tag 7012
  regulationID : Option (Terminated 1)  -- tag 7013
  noTradeFeat : Option (Terminated 1)  -- tag 7713
  noTradeKey : Option (Terminated 1)  -- tag 7714
  shortMarkingExempt : Option (Terminated 1)  -- tag 7729
  bIDSOriginatingBroker : Option (Terminated 1)  -- tag 8073
  bIDSExecBroker : Option (Terminated 1)  -- tag 8090
  bIDSContraExecBroker : Option (Terminated 1)  -- tag 8091
  feeCode : Option (Terminated 1)  -- tag 9882
  printFeeCode : Option (Terminated 1)  -- tag 9883
  lEICustomerAccount : Option (Terminated 1)  -- tag 18025
  lEIAlgorithmID : Option (Terminated 1)  -- tag 18026
  customerLEI : Option (Terminated 1)  -- tag 18027
  brokerLEI : Option (Terminated 1)  -- tag 18028
  traderID : Terminated 1  -- tag 22010
  lastCapacity : Option (Terminated 1)  -- tag 29
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSellNakedQty : Option (Terminated 1)  -- tag 6803
  shortSellCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSellLongQty : Option (Terminated 1)  -- tag 6805
  transactID : Option (Terminated 1)  -- tag 6807
  originOfTrans : Option (Terminated 1)  -- tag 8138
  intermediaryID : Option (Terminated 1)  -- tag 8139
  directedWholesaleIndic : Option (Terminated 1)  -- tag 8140
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  orderRestrictions : Option (Terminated 1)  -- tag 8182
  crossType : Option (Terminated 1)  -- tag 8183
  cashMargin : Option (Terminated 1)  -- tag 544
  bIDSNBBPrice : Option (Terminated 1)  -- tag 8019
  bIDSNBOPrice : Option (Terminated 1)  -- tag 8020
  bIDSNBBOTimestamp : Option (Terminated 1)  -- tag 8021
  primaryLastPx : Option (Terminated 1)  -- tag 8031
  orderClassification : Option (Terminated 1)  -- tag 8093
  toSTNeTOrderID : Option (Terminated 1)  -- tag 8101
  toSTNeTExecutionID : Option (Terminated 1)  -- tag 8102
  toSTNeTTransactTime : Option (Terminated 1)  -- tag 8106
  noSelfTrade : Option (Terminated 1)  -- tag 8174
  noPartyIDs : Option (Terminated 1)  -- tag 453
  senderTime : Option (Terminated 1)  -- tag 8071
  noBIDSAllotmentEntities : Option (Terminated 1)  -- tag 8080

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 57] record.execRefID,
   Part.required [50, 48] record.execTransType,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 48] record.lastMkt,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [52, 55] record.rule80A,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [55, 54] record.execBroker,
   Part.required [49, 48, 57] record.clientID,
   Part.required [49, 49, 48] record.minQty,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 56] record.effectiveTime,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [55, 54, 57] record.trdRegTimestamp,
   Part.required [55, 55, 53] record.bookingType,
   Part.optional [57, 55, 51, 48] record.lastLiquidityInd,
   Part.optional [49, 57, 48, 51] record.regulatoryTradeID,
   Part.optional [49, 57, 48, 54] record.regulatoryTradeIDType,
   Part.optional [49, 57, 48, 55] record.noRegulatoryTradeIDs,
   Part.optional [53, 55, 48, 48] record.locateBroker,
   Part.optional [53, 55, 48, 49] record.locateIdentifier,
   Part.optional [56, 48, 49, 55] record.bIDSPriceProtection,
   Part.optional [56, 48, 49, 54] record.tradingVenueRegulatoryTradeID,
   Part.optional [56, 48, 50, 54] record.bIDSTradeId,
   Part.required [56, 48, 53, 50] record.bIDSReportingType,
   Part.optional [56, 48, 54, 51] record.bIDSUniqueClOrdID,
   Part.optional [56, 48, 54, 55] record.bIDSSponsoredTraderName,
   Part.optional [56, 48, 54, 57] record.bIDSCentralCounterparty,
   Part.optional [56, 48, 55, 48] record.targetContraFirm,
   Part.optional [56, 48, 56, 50] record.bIDSAEFirm,
   Part.optional [56, 48, 56, 54] record.bIDSAEVolume,
   Part.optional [56, 48, 56, 56] record.bIDSAEBookingType,
   Part.optional [56, 48, 56, 57] record.bIDSAEFilledVolume,
   Part.optional [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm,
   Part.optional [49, 55, 50, 52] record.lEIOrderOrigination,
   Part.optional [50, 56, 56, 51] record.lEIRoutingArrangementIndicator,
   Part.optional [54, 55, 54, 51] record.uMIRRegulationID,
   Part.optional [54, 55, 55, 54] record.principalTrade,
   Part.optional [54, 55, 55, 55] record.washTradeIndicator,
   Part.optional [55, 48, 48, 51] record.programTrade,
   Part.optional [55, 48, 49, 50] record.anonymous,
   Part.optional [55, 48, 49, 51] record.regulationID,
   Part.optional [55, 55, 49, 51] record.noTradeFeat,
   Part.optional [55, 55, 49, 52] record.noTradeKey,
   Part.optional [55, 55, 50, 57] record.shortMarkingExempt,
   Part.optional [56, 48, 55, 51] record.bIDSOriginatingBroker,
   Part.optional [56, 48, 57, 48] record.bIDSExecBroker,
   Part.optional [56, 48, 57, 49] record.bIDSContraExecBroker,
   Part.optional [57, 56, 56, 50] record.feeCode,
   Part.optional [57, 56, 56, 51] record.printFeeCode,
   Part.optional [49, 56, 48, 50, 53] record.lEICustomerAccount,
   Part.optional [49, 56, 48, 50, 54] record.lEIAlgorithmID,
   Part.optional [49, 56, 48, 50, 55] record.customerLEI,
   Part.optional [49, 56, 48, 50, 56] record.brokerLEI,
   Part.required [50, 50, 48, 49, 48] record.traderID,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSellNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSellCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSellLongQty,
   Part.optional [54, 56, 48, 55] record.transactID,
   Part.optional [56, 49, 51, 56] record.originOfTrans,
   Part.optional [56, 49, 51, 57] record.intermediaryID,
   Part.optional [56, 49, 52, 48] record.directedWholesaleIndic,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.optional [56, 49, 56, 50] record.orderRestrictions,
   Part.optional [56, 49, 56, 51] record.crossType,
   Part.optional [53, 52, 52] record.cashMargin,
   Part.optional [56, 48, 49, 57] record.bIDSNBBPrice,
   Part.optional [56, 48, 50, 48] record.bIDSNBOPrice,
   Part.optional [56, 48, 50, 49] record.bIDSNBBOTimestamp,
   Part.optional [56, 48, 51, 49] record.primaryLastPx,
   Part.optional [56, 48, 57, 51] record.orderClassification,
   Part.optional [56, 49, 48, 49] record.toSTNeTOrderID,
   Part.optional [56, 49, 48, 50] record.toSTNeTExecutionID,
   Part.optional [56, 49, 48, 54] record.toSTNeTTransactTime,
   Part.optional [56, 49, 55, 52] record.noSelfTrade,
   Part.optional [52, 53, 51] record.noPartyIDs,
   Part.optional [56, 48, 55, 49] record.senderTime,
   Part.optional [56, 48, 56, 48] record.noBIDSAllotmentEntities]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 53]], [[49, 52]], [[49, 55]], [[49, 56]], [[49, 57]], [[50, 48]], [[50, 50]], [[51, 48]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[52, 55]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[54, 53]], [[55, 54]], [[49, 48, 57]], [[49, 49, 48]], [[49, 49, 52]], [[49, 50, 54]], [[49, 53, 49]], [[49, 54, 56]], [[50, 48, 55]], [[50, 49, 49]], [[51, 56, 56]], [[51, 56, 57]], [[52, 51, 57]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[53, 50, 56]], [[55, 54, 57]], [[55, 55, 53]], [[57, 55, 51, 48]], [[49, 57, 48, 51]], [[49, 57, 48, 54]], [[49, 57, 48, 55]], [[53, 55, 48, 48]], [[53, 55, 48, 49]], [[56, 48, 49, 55]], [[56, 48, 49, 54]], [[56, 48, 50, 54]], [[56, 48, 53, 50]], [[56, 48, 54, 51]], [[56, 48, 54, 55]], [[56, 48, 54, 57]], [[56, 48, 55, 48]], [[56, 48, 56, 50]], [[56, 48, 56, 54]], [[56, 48, 56, 56]], [[56, 48, 56, 57]], [[50, 48, 48, 49, 51]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 54, 51]], [[54, 55, 55, 54]], [[54, 55, 55, 55]], [[55, 48, 48, 51]], [[55, 48, 49, 50]], [[55, 48, 49, 51]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[55, 55, 50, 57]], [[56, 48, 55, 51]], [[56, 48, 57, 48]], [[56, 48, 57, 49]], [[57, 56, 56, 50]], [[57, 56, 56, 51]], [[49, 56, 48, 50, 53]], [[49, 56, 48, 50, 54]], [[49, 56, 48, 50, 55]], [[49, 56, 48, 50, 56]], [[50, 50, 48, 49, 48]], [[50, 57]], [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[54, 56, 48, 55]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 50]], [[56, 49, 56, 51]], [[53, 52, 52]], [[56, 48, 49, 57]], [[56, 48, 50, 48]], [[56, 48, 50, 49]], [[56, 48, 51, 49]], [[56, 48, 57, 51]], [[56, 49, 48, 49]], [[56, 49, 48, 50]], [[56, 49, 48, 54]], [[56, 49, 55, 52]], [[52, 53, 51]], [[56, 48, 55, 49]], [[56, 48, 56, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readRequired [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execTransType ← readRequired [50, 48] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let rule80A ← readRequired [52, 55] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readRequired [55, 54] tokens
  let clientID ← readRequired [49, 48, 57] tokens
  let minQty ← readRequired [49, 49, 48] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let effectiveTime ← readRequired [49, 54, 56] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let trdRegTimestamp ← readOptional [55, 54, 57] tokens
  let bookingType ← readRequired [55, 55, 53] tokens
  let lastLiquidityInd ← readOptional [57, 55, 51, 48] tokens
  let regulatoryTradeID ← readOptional [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readOptional [49, 57, 48, 54] tokens
  let noRegulatoryTradeIDs ← readOptional [49, 57, 48, 55] tokens
  let locateBroker ← readOptional [53, 55, 48, 48] tokens
  let locateIdentifier ← readOptional [53, 55, 48, 49] tokens
  let bIDSPriceProtection ← readOptional [56, 48, 49, 55] tokens
  let tradingVenueRegulatoryTradeID ← readOptional [56, 48, 49, 54] tokens
  let bIDSTradeId ← readOptional [56, 48, 50, 54] tokens
  let bIDSReportingType ← readRequired [56, 48, 53, 50] tokens
  let bIDSUniqueClOrdID ← readOptional [56, 48, 54, 51] tokens
  let bIDSSponsoredTraderName ← readOptional [56, 48, 54, 55] tokens
  let bIDSCentralCounterparty ← readOptional [56, 48, 54, 57] tokens
  let targetContraFirm ← readOptional [56, 48, 55, 48] tokens
  let bIDSAEFirm ← readOptional [56, 48, 56, 50] tokens
  let bIDSAEVolume ← readOptional [56, 48, 56, 54] tokens
  let bIDSAEBookingType ← readOptional [56, 48, 56, 56] tokens
  let bIDSAEFilledVolume ← readOptional [56, 48, 56, 57] tokens
  let partyIDOrderOriginationFirm ← readOptional [50, 48, 48, 49, 51] tokens
  let lEIOrderOrigination ← readOptional [49, 55, 50, 52] tokens
  let lEIRoutingArrangementIndicator ← readOptional [50, 56, 56, 51] tokens
  let uMIRRegulationID ← readOptional [54, 55, 54, 51] tokens
  let principalTrade ← readOptional [54, 55, 55, 54] tokens
  let washTradeIndicator ← readOptional [54, 55, 55, 55] tokens
  let programTrade ← readOptional [55, 48, 48, 51] tokens
  let anonymous ← readOptional [55, 48, 49, 50] tokens
  let regulationID ← readOptional [55, 48, 49, 51] tokens
  let noTradeFeat ← readOptional [55, 55, 49, 51] tokens
  let noTradeKey ← readOptional [55, 55, 49, 52] tokens
  let shortMarkingExempt ← readOptional [55, 55, 50, 57] tokens
  let bIDSOriginatingBroker ← readOptional [56, 48, 55, 51] tokens
  let bIDSExecBroker ← readOptional [56, 48, 57, 48] tokens
  let bIDSContraExecBroker ← readOptional [56, 48, 57, 49] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  let printFeeCode ← readOptional [57, 56, 56, 51] tokens
  let lEICustomerAccount ← readOptional [49, 56, 48, 50, 53] tokens
  let lEIAlgorithmID ← readOptional [49, 56, 48, 50, 54] tokens
  let customerLEI ← readOptional [49, 56, 48, 50, 55] tokens
  let brokerLEI ← readOptional [49, 56, 48, 50, 56] tokens
  let traderID ← readRequired [50, 50, 48, 49, 48] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSellNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSellCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSellLongQty ← readOptional [54, 56, 48, 53] tokens
  let transactID ← readOptional [54, 56, 48, 55] tokens
  let originOfTrans ← readOptional [56, 49, 51, 56] tokens
  let intermediaryID ← readOptional [56, 49, 51, 57] tokens
  let directedWholesaleIndic ← readOptional [56, 49, 52, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let orderRestrictions ← readOptional [56, 49, 56, 50] tokens
  let crossType ← readOptional [56, 49, 56, 51] tokens
  let cashMargin ← readOptional [53, 52, 52] tokens
  let bIDSNBBPrice ← readOptional [56, 48, 49, 57] tokens
  let bIDSNBOPrice ← readOptional [56, 48, 50, 48] tokens
  let bIDSNBBOTimestamp ← readOptional [56, 48, 50, 49] tokens
  let primaryLastPx ← readOptional [56, 48, 51, 49] tokens
  let orderClassification ← readOptional [56, 48, 57, 51] tokens
  let toSTNeTOrderID ← readOptional [56, 49, 48, 49] tokens
  let toSTNeTExecutionID ← readOptional [56, 49, 48, 50] tokens
  let toSTNeTTransactTime ← readOptional [56, 49, 48, 54] tokens
  let noSelfTrade ← readOptional [56, 49, 55, 52] tokens
  let noPartyIDs ← readOptional [52, 53, 51] tokens
  let senderTime ← readOptional [56, 48, 55, 49] tokens
  let noBIDSAllotmentEntities ← readOptional [56, 48, 56, 48] tokens
  pure { account, avgPx, clOrdID, currency, cumQty, execID, execInst, execRefID, execTransType, iDSource, lastMkt, orderID, orderQty, ordStatus, ordType, price, rule80A, securityID, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, clientID, minQty, locateReqd, expireTime, leavesQty, effectiveTime, securityExchange, pegDifference, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, trdRegTimestamp, bookingType, lastLiquidityInd, regulatoryTradeID, regulatoryTradeIDType, noRegulatoryTradeIDs, locateBroker, locateIdentifier, bIDSPriceProtection, tradingVenueRegulatoryTradeID, bIDSTradeId, bIDSReportingType, bIDSUniqueClOrdID, bIDSSponsoredTraderName, bIDSCentralCounterparty, targetContraFirm, bIDSAEFirm, bIDSAEVolume, bIDSAEBookingType, bIDSAEFilledVolume, partyIDOrderOriginationFirm, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRRegulationID, principalTrade, washTradeIndicator, programTrade, anonymous, regulationID, noTradeFeat, noTradeKey, shortMarkingExempt, bIDSOriginatingBroker, bIDSExecBroker, bIDSContraExecBroker, feeCode, printFeeCode, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, traderID, lastCapacity, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, transactID, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, orderRestrictions, crossType, cashMargin, bIDSNBBPrice, bIDSNBOPrice, bIDSNBBOTimestamp, primaryLastPx, orderClassification, toSTNeTOrderID, toSTNeTExecutionID, toSTNeTTransactTime, noSelfTrade, noPartyIDs, senderTime, noBIDSAllotmentEntities }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have rule80A := readRequired_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have execBroker := readRequired_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clientID := readRequired_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have minQty := readRequired_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have effectiveTime := readRequired_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have trdRegTimestamp := readOptional_part [55, 54, 57] record.trdRegTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have bookingType := readRequired_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [57, 55, 51, 48] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have regulatoryTradeID := readOptional_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have regulatoryTradeIDType := readOptional_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have noRegulatoryTradeIDs := readOptional_part [49, 57, 48, 55] record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have locateIdentifier := readOptional_part [53, 55, 48, 49] record.locateIdentifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have bIDSPriceProtection := readOptional_part [56, 48, 49, 55] record.bIDSPriceProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have tradingVenueRegulatoryTradeID := readOptional_part [56, 48, 49, 54] record.tradingVenueRegulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have bIDSTradeId := readOptional_part [56, 48, 50, 54] record.bIDSTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have bIDSReportingType := readRequired_part [56, 48, 53, 50] record.bIDSReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have bIDSUniqueClOrdID := readOptional_part [56, 48, 54, 51] record.bIDSUniqueClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have bIDSSponsoredTraderName := readOptional_part [56, 48, 54, 55] record.bIDSSponsoredTraderName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have bIDSCentralCounterparty := readOptional_part [56, 48, 54, 57] record.bIDSCentralCounterparty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have targetContraFirm := readOptional_part [56, 48, 55, 48] record.targetContraFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have bIDSAEFirm := readOptional_part [56, 48, 56, 50] record.bIDSAEFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have bIDSAEVolume := readOptional_part [56, 48, 56, 54] record.bIDSAEVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have bIDSAEBookingType := readOptional_part [56, 48, 56, 56] record.bIDSAEBookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have bIDSAEFilledVolume := readOptional_part [56, 48, 56, 57] record.bIDSAEFilledVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have partyIDOrderOriginationFirm := readOptional_part [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have lEIOrderOrigination := readOptional_part [49, 55, 50, 52] record.lEIOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have lEIRoutingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.lEIRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have principalTrade := readOptional_part [54, 55, 55, 54] record.principalTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  have washTradeIndicator := readOptional_part [54, 55, 55, 55] record.washTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 64 (by decide +kernel)))
  have programTrade := readOptional_part [55, 48, 48, 51] record.programTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 65 (by decide +kernel)))
  have anonymous := readOptional_part [55, 48, 49, 50] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 66 (by decide +kernel)))
  have regulationID := readOptional_part [55, 48, 49, 51] record.regulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 67 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 68 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 69 (by decide +kernel)))
  have shortMarkingExempt := readOptional_part [55, 55, 50, 57] record.shortMarkingExempt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 70 (by decide +kernel)))
  have bIDSOriginatingBroker := readOptional_part [56, 48, 55, 51] record.bIDSOriginatingBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 71 (by decide +kernel)))
  have bIDSExecBroker := readOptional_part [56, 48, 57, 48] record.bIDSExecBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 72 (by decide +kernel)))
  have bIDSContraExecBroker := readOptional_part [56, 48, 57, 49] record.bIDSContraExecBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 73 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 74 (by decide +kernel)))
  have printFeeCode := readOptional_part [57, 56, 56, 51] record.printFeeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 75 (by decide +kernel)))
  have lEICustomerAccount := readOptional_part [49, 56, 48, 50, 53] record.lEICustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 76 (by decide +kernel)))
  have lEIAlgorithmID := readOptional_part [49, 56, 48, 50, 54] record.lEIAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 77 (by decide +kernel)))
  have customerLEI := readOptional_part [49, 56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 78 (by decide +kernel)))
  have brokerLEI := readOptional_part [49, 56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 79 (by decide +kernel)))
  have traderID := readRequired_part [50, 50, 48, 49, 48] record.traderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 80 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 81 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 82 (by decide +kernel)))
  have shortSellNakedQty := readOptional_part [54, 56, 48, 51] record.shortSellNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 83 (by decide +kernel)))
  have shortSellCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSellCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 84 (by decide +kernel)))
  have shortSellLongQty := readOptional_part [54, 56, 48, 53] record.shortSellLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 85 (by decide +kernel)))
  have transactID := readOptional_part [54, 56, 48, 55] record.transactID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 86 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 87 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 88 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 89 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 90 (by decide +kernel)))
  have orderRestrictions := readOptional_part [56, 49, 56, 50] record.orderRestrictions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 91 (by decide +kernel)))
  have crossType := readOptional_part [56, 49, 56, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 92 (by decide +kernel)))
  have cashMargin := readOptional_part [53, 52, 52] record.cashMargin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 93 (by decide +kernel)))
  have bIDSNBBPrice := readOptional_part [56, 48, 49, 57] record.bIDSNBBPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 94 (by decide +kernel)))
  have bIDSNBOPrice := readOptional_part [56, 48, 50, 48] record.bIDSNBOPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 95 (by decide +kernel)))
  have bIDSNBBOTimestamp := readOptional_part [56, 48, 50, 49] record.bIDSNBBOTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 96 (by decide +kernel)))
  have primaryLastPx := readOptional_part [56, 48, 51, 49] record.primaryLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 97 (by decide +kernel)))
  have orderClassification := readOptional_part [56, 48, 57, 51] record.orderClassification tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 98 (by decide +kernel)))
  have toSTNeTOrderID := readOptional_part [56, 49, 48, 49] record.toSTNeTOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 99 (by decide +kernel)))
  have toSTNeTExecutionID := readOptional_part [56, 49, 48, 50] record.toSTNeTExecutionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 100 (by decide +kernel)))
  have toSTNeTTransactTime := readOptional_part [56, 49, 48, 54] record.toSTNeTTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 101 (by decide +kernel)))
  have noSelfTrade := readOptional_part [56, 49, 55, 52] record.noSelfTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 102 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 103 (by decide +kernel)))
  have senderTime := readOptional_part [56, 48, 55, 49] record.senderTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 104 (by decide +kernel)))
  have noBIDSAllotmentEntities := readOptional_part [56, 48, 56, 48] record.noBIDSAllotmentEntities tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 105 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, currency, cumQty, execID, execInst, execRefID, execTransType, iDSource, lastMkt, orderID, orderQty, ordStatus, ordType, price, rule80A, securityID, side, symbol, timeInForce, transactTime, symbolSfx, execBroker, clientID, minQty, locateReqd, expireTime, leavesQty, effectiveTime, securityExchange, pegDifference, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, trdRegTimestamp, bookingType, lastLiquidityInd, regulatoryTradeID, regulatoryTradeIDType, noRegulatoryTradeIDs, locateBroker, locateIdentifier, bIDSPriceProtection, tradingVenueRegulatoryTradeID, bIDSTradeId, bIDSReportingType, bIDSUniqueClOrdID, bIDSSponsoredTraderName, bIDSCentralCounterparty, targetContraFirm, bIDSAEFirm, bIDSAEVolume, bIDSAEBookingType, bIDSAEFilledVolume, partyIDOrderOriginationFirm, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRRegulationID, principalTrade, washTradeIndicator, programTrade, anonymous, regulationID, noTradeFeat, noTradeKey, shortMarkingExempt, bIDSOriginatingBroker, bIDSExecBroker, bIDSContraExecBroker, feeCode, printFeeCode, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, traderID, lastCapacity, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, transactID, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, orderRestrictions, crossType, cashMargin, bIDSNBBPrice, bIDSNBOPrice, bIDSNBBOTimestamp, primaryLastPx, orderClassification, toSTNeTOrderID, toSTNeTExecutionID, toSTNeTTransactTime, noSelfTrade, noPartyIDs, senderTime, noBIDSAllotmentEntities, some_bind] <;> rfl

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
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  contraBroker : Option (Terminated 1)  -- tag 375

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [51, 55, 53] record.contraBroker]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]], [[51, 55, 53]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  pure { lastShares, lastPx, contraBroker }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, lastShares, lastPx, contraBroker, some_bind] <;> rfl

structure ExecutionReportFill where
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  contraBroker : Option (Terminated 1)  -- tag 375

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [51, 55, 53] record.contraBroker]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]], [[51, 55, 53]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  pure { lastShares, lastPx, contraBroker }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, lastShares, lastPx, contraBroker, some_bind] <;> rfl

structure ExecutionReportCanceled where
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[53, 56]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  pure { origClOrdID, text }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, origClOrdID, text, some_bind] <;> rfl

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

structure ExecutionReportExpired

def ExecutionReportExpired.parts (_ : ExecutionReportExpired) : List Part :=
  []

def ExecutionReportExpired.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportExpired.shape (record : ExecutionReportExpired) : record.parts.map Part.tags = ExecutionReportExpired.tags := rfl

def ExecutionReportExpired.decode (_ : List Token) : Option ExecutionReportExpired := some {}

theorem ExecutionReportExpired.decode_agrees (record : ExecutionReportExpired) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportExpired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportExpired.decode tokens = some record := by
  rfl

inductive Message where
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired)

def Message.tokens : Message → List Token
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportExpired header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts)

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
          else if key.val = [67] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportExpired.decode rest
              pure (.executionReportExpired header r0 r1)
            else none
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

theorem Message.decode_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decode (Message.tokens (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportExpired.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportExpired.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportExpired.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decode_executionReportExpired header r0 r1

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

theorem Message.decodeBytes_executionReportExpired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportExpired) :
    Message.decodeBytes (Message.encode (.executionReportExpired header r0 r1)) = some (.executionReportExpired header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[67], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExpired.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportExpired header r0 r1

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportExpired header r0 r1 => exact Message.decodeBytes_executionReportExpired header r0 r1

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeBidsjapanDropcopyFixV873
