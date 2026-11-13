import Wire

/-!
# Chicago Board Options Exchange Drop Copy v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCxaequitiesDropcopyFixV10Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  pure { senderCompID, senderSubID, targetCompID }

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
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, some_bind] <;> rfl

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdID : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execTransType : Terminated 1  -- tag 20
  orderId : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  orderCapacity : Option (Terminated 1)  -- tag 47
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  clientID : Option (Terminated 1)  -- tag 109
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  leavesQty : Terminated 1  -- tag 151
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Terminated 1  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  undisclosed : Option (Terminated 1)  -- tag 6801
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSaleNakedQty : Option (Terminated 1)  -- tag 6803
  shortSaleCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSaleLongQty : Option (Terminated 1)  -- tag 6805
  riskGroupID : Option (Terminated 1)  -- tag 7699
  noTradeFeat : Option (Terminated 1)  -- tag 7713
  noTradeKey : Option (Terminated 1)  -- tag 7714
  mEQSE : Option (Terminated 1)  -- tag 8081
  originOfTrans : Option (Terminated 1)  -- tag 8138
  intermediaryID : Option (Terminated 1)  -- tag 8139
  directedWholesaleIndic : Option (Terminated 1)  -- tag 8140
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  brokerPreferencing : Option (Terminated 1)  -- tag 8182
  routingInst : Option (Terminated 1)  -- tag 9303
  displayIndicator : Option (Terminated 1)  -- tag 9479
  modifySequence : Option (Terminated 1)  -- tag 9617
  origCompID : Terminated 1  -- tag 9688
  origSubID : Terminated 1  -- tag 9689
  tradeLiquidityIndicator : Terminated 1  -- tag 9730

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 55] record.orderId,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.orderCapacity,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [54, 56, 48, 49] record.undisclosed,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSaleNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSaleCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSaleLongQty,
   Part.optional [55, 54, 57, 57] record.riskGroupID,
   Part.optional [55, 55, 49, 51] record.noTradeFeat,
   Part.optional [55, 55, 49, 52] record.noTradeKey,
   Part.optional [56, 48, 56, 49] record.mEQSE,
   Part.optional [56, 49, 51, 56] record.originOfTrans,
   Part.optional [56, 49, 51, 57] record.intermediaryID,
   Part.optional [56, 49, 52, 48] record.directedWholesaleIndic,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.optional [56, 49, 56, 50] record.brokerPreferencing,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 55, 57] record.displayIndicator,
   Part.optional [57, 54, 49, 55] record.modifySequence,
   Part.required [57, 54, 56, 56] record.origCompID,
   Part.required [57, 54, 56, 57] record.origSubID,
   Part.required [57, 55, 51, 48] record.tradeLiquidityIndicator]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[49, 56]], [[50, 48]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[52, 55]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 48, 57]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[49, 53, 49]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[54, 56, 48, 49]], [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[55, 54, 57, 57]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[56, 48, 56, 49]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 50]], [[57, 51, 48, 51]], [[57, 52, 55, 57]], [[57, 54, 49, 55]], [[57, 54, 56, 56]], [[57, 54, 56, 57]], [[57, 55, 51, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execTransType ← readRequired [50, 48] tokens
  let orderId ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderCapacity ← readOptional [52, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readRequired [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let undisclosed ← readOptional [54, 56, 48, 49] tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSaleNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSaleCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSaleLongQty ← readOptional [54, 56, 48, 53] tokens
  let riskGroupID ← readOptional [55, 54, 57, 57] tokens
  let noTradeFeat ← readOptional [55, 55, 49, 51] tokens
  let noTradeKey ← readOptional [55, 55, 49, 52] tokens
  let mEQSE ← readOptional [56, 48, 56, 49] tokens
  let originOfTrans ← readOptional [56, 49, 51, 56] tokens
  let intermediaryID ← readOptional [56, 49, 51, 57] tokens
  let directedWholesaleIndic ← readOptional [56, 49, 52, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let brokerPreferencing ← readOptional [56, 49, 56, 50] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let displayIndicator ← readOptional [57, 52, 55, 57] tokens
  let modifySequence ← readOptional [57, 54, 49, 55] tokens
  let origCompID ← readRequired [57, 54, 56, 56] tokens
  let origSubID ← readRequired [57, 54, 56, 57] tokens
  let tradeLiquidityIndicator ← readRequired [57, 55, 51, 48] tokens
  pure { account, avgPx, clOrdID, cumQty, execID, execInst, execTransType, orderId, orderQty, ordStatus, ordType, price, orderCapacity, side, symbol, timeInForce, transactTime, clientID, minQty, maxFloor, expireTime, leavesQty, securityExchange, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSaleNakedQty, shortSaleCoveredQty, shortSaleLongQty, riskGroupID, noTradeFeat, noTradeKey, mEQSE, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator, modifySequence, origCompID, origSubID, tradeLiquidityIndicator }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderId := readRequired_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderCapacity := readOptional_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clearingFirm := readRequired_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have undisclosed := readOptional_part [54, 56, 48, 49] record.undisclosed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have shortSaleNakedQty := readOptional_part [54, 56, 48, 51] record.shortSaleNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have shortSaleCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSaleCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have shortSaleLongQty := readOptional_part [54, 56, 48, 53] record.shortSaleLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have riskGroupID := readOptional_part [55, 54, 57, 57] record.riskGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have mEQSE := readOptional_part [56, 48, 56, 49] record.mEQSE tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have brokerPreferencing := readOptional_part [56, 49, 56, 50] record.brokerPreferencing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have displayIndicator := readOptional_part [57, 52, 55, 57] record.displayIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have modifySequence := readOptional_part [57, 54, 49, 55] record.modifySequence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have origCompID := readRequired_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have origSubID := readRequired_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tradeLiquidityIndicator := readRequired_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, cumQty, execID, execInst, execTransType, orderId, orderQty, ordStatus, ordType, price, orderCapacity, side, symbol, timeInForce, transactTime, clientID, minQty, maxFloor, expireTime, leavesQty, securityExchange, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSaleNakedQty, shortSaleCoveredQty, shortSaleLongQty, riskGroupID, noTradeFeat, noTradeKey, mEQSE, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator, modifySequence, origCompID, origSubID, tradeLiquidityIndicator, some_bind] <;> rfl

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
  lastCapacity : Option (Terminated 1)  -- tag 29
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  noContraBrokers : Option (Terminated 1)  -- tag 382
  transactID : Terminated 1  -- tag 6807
  priceImprovement : Option (Terminated 1)  -- tag 639
  crossType : Option (Terminated 1)  -- tag 8183
  bookingPurposeTrade : Option (Terminated 1)  -- tag 8184
  contraTradePA : Option (Terminated 1)  -- tag 9862
  feeCode : Option (Terminated 1)  -- tag 9882

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.optional [50, 57] record.lastCapacity,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.required [54, 56, 48, 55] record.transactID,
   Part.optional [54, 51, 57] record.priceImprovement,
   Part.optional [56, 49, 56, 51] record.crossType,
   Part.optional [56, 49, 56, 52] record.bookingPurposeTrade,
   Part.optional [57, 56, 54, 50] record.contraTradePA,
   Part.optional [57, 56, 56, 50] record.feeCode]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[50, 57]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 56, 50]], [[54, 56, 48, 55]], [[54, 51, 57]], [[56, 49, 56, 51]], [[56, 49, 56, 52]], [[57, 56, 54, 50]], [[57, 56, 56, 50]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let lastCapacity ← readOptional [50, 57] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let transactID ← readRequired [54, 56, 48, 55] tokens
  let priceImprovement ← readOptional [54, 51, 57] tokens
  let crossType ← readOptional [56, 49, 56, 51] tokens
  let bookingPurposeTrade ← readOptional [56, 49, 56, 52] tokens
  let contraTradePA ← readOptional [57, 56, 54, 50] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { lastCapacity, lastMkt, lastPx, lastShares, noContraBrokers, transactID, priceImprovement, crossType, bookingPurposeTrade, contraTradePA, feeCode }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactID := readRequired_part [54, 56, 48, 55] record.transactID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have priceImprovement := readOptional_part [54, 51, 57] record.priceImprovement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have crossType := readOptional_part [56, 49, 56, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have bookingPurposeTrade := readOptional_part [56, 49, 56, 52] record.bookingPurposeTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contraTradePA := readOptional_part [57, 56, 54, 50] record.contraTradePA tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, lastCapacity, lastMkt, lastPx, lastShares, noContraBrokers, transactID, priceImprovement, crossType, bookingPurposeTrade, contraTradePA, feeCode, some_bind] <;> rfl

structure ExecutionReportFill where
  lastCapacity : Option (Terminated 1)  -- tag 29
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  noContraBrokers : Option (Terminated 1)  -- tag 382
  transactID : Terminated 1  -- tag 6807
  priceImprovement : Option (Terminated 1)  -- tag 639
  crossType : Option (Terminated 1)  -- tag 8183
  bookingPurposeTrade : Option (Terminated 1)  -- tag 8184
  contraTradePA : Option (Terminated 1)  -- tag 9862
  feeCode : Option (Terminated 1)  -- tag 9882

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.optional [50, 57] record.lastCapacity,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.required [54, 56, 48, 55] record.transactID,
   Part.optional [54, 51, 57] record.priceImprovement,
   Part.optional [56, 49, 56, 51] record.crossType,
   Part.optional [56, 49, 56, 52] record.bookingPurposeTrade,
   Part.optional [57, 56, 54, 50] record.contraTradePA,
   Part.optional [57, 56, 56, 50] record.feeCode]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[50, 57]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 56, 50]], [[54, 56, 48, 55]], [[54, 51, 57]], [[56, 49, 56, 51]], [[56, 49, 56, 52]], [[57, 56, 54, 50]], [[57, 56, 56, 50]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let lastCapacity ← readOptional [50, 57] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let transactID ← readRequired [54, 56, 48, 55] tokens
  let priceImprovement ← readOptional [54, 51, 57] tokens
  let crossType ← readOptional [56, 49, 56, 51] tokens
  let bookingPurposeTrade ← readOptional [56, 49, 56, 52] tokens
  let contraTradePA ← readOptional [57, 56, 54, 50] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { lastCapacity, lastMkt, lastPx, lastShares, noContraBrokers, transactID, priceImprovement, crossType, bookingPurposeTrade, contraTradePA, feeCode }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactID := readRequired_part [54, 56, 48, 55] record.transactID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have priceImprovement := readOptional_part [54, 51, 57] record.priceImprovement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have crossType := readOptional_part [56, 49, 56, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have bookingPurposeTrade := readOptional_part [56, 49, 56, 52] record.bookingPurposeTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have contraTradePA := readOptional_part [57, 56, 54, 50] record.contraTradePA tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, lastCapacity, lastMkt, lastPx, lastShares, noContraBrokers, transactID, priceImprovement, crossType, bookingPurposeTrade, contraTradePA, feeCode, some_bind] <;> rfl

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
  text : Option (Terminated 1)  -- tag 58
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  preventedTradePx : Option (Terminated 1)  -- tag 7903
  preventedTradeQty : Option (Terminated 1)  -- tag 7904
  preventedTradeLiquidityIndicator : Option (Terminated 1)  -- tag 7905

def ExecutionReportCanceled.parts (record : ExecutionReportCanceled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [55, 57, 48, 51] record.preventedTradePx,
   Part.optional [55, 57, 48, 52] record.preventedTradeQty,
   Part.optional [55, 57, 48, 53] record.preventedTradeLiquidityIndicator]

def ExecutionReportCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[53, 56]], [[49, 57, 56]], [[55, 57, 48, 51]], [[55, 57, 48, 52]], [[55, 57, 48, 53]]]

theorem ExecutionReportCanceled.shape (record : ExecutionReportCanceled) : record.parts.map Part.tags = ExecutionReportCanceled.tags := rfl

def ExecutionReportCanceled.decode (tokens : List Token) : Option ExecutionReportCanceled := do
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let preventedTradePx ← readOptional [55, 57, 48, 51] tokens
  let preventedTradeQty ← readOptional [55, 57, 48, 52] tokens
  let preventedTradeLiquidityIndicator ← readOptional [55, 57, 48, 53] tokens
  pure { origClOrdID, text, secondaryOrderID, preventedTradePx, preventedTradeQty, preventedTradeLiquidityIndicator }

theorem ExecutionReportCanceled.decode_agrees (record : ExecutionReportCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCanceled.decode tokens = some record := by
  have distinct : ExecutionReportCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have preventedTradePx := readOptional_part [55, 57, 48, 51] record.preventedTradePx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have preventedTradeQty := readOptional_part [55, 57, 48, 52] record.preventedTradeQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have preventedTradeLiquidityIndicator := readOptional_part [55, 57, 48, 53] record.preventedTradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportCanceled.decode, origClOrdID, text, secondaryOrderID, preventedTradePx, preventedTradeQty, preventedTradeLiquidityIndicator, some_bind] <;> rfl

structure ExecutionReportReplaced where
  origClOrdID : Option (Terminated 1)  -- tag 41
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  workingPrice : Option (Terminated 1)  -- tag 9690
  preventedTradePx : Option (Terminated 1)  -- tag 7903
  preventedTradeQty : Option (Terminated 1)  -- tag 7904
  preventedTradeLiquidityIndicator : Option (Terminated 1)  -- tag 7905

def ExecutionReportReplaced.parts (record : ExecutionReportReplaced) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [57, 54, 57, 48] record.workingPrice,
   Part.optional [55, 57, 48, 51] record.preventedTradePx,
   Part.optional [55, 57, 48, 52] record.preventedTradeQty,
   Part.optional [55, 57, 48, 53] record.preventedTradeLiquidityIndicator]

def ExecutionReportReplaced.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 57, 56]], [[57, 54, 57, 48]], [[55, 57, 48, 51]], [[55, 57, 48, 52]], [[55, 57, 48, 53]]]

theorem ExecutionReportReplaced.shape (record : ExecutionReportReplaced) : record.parts.map Part.tags = ExecutionReportReplaced.tags := rfl

def ExecutionReportReplaced.decode (tokens : List Token) : Option ExecutionReportReplaced := do
  let origClOrdID ← readOptional [52, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let workingPrice ← readOptional [57, 54, 57, 48] tokens
  let preventedTradePx ← readOptional [55, 57, 48, 51] tokens
  let preventedTradeQty ← readOptional [55, 57, 48, 52] tokens
  let preventedTradeLiquidityIndicator ← readOptional [55, 57, 48, 53] tokens
  pure { origClOrdID, secondaryOrderID, workingPrice, preventedTradePx, preventedTradeQty, preventedTradeLiquidityIndicator }

theorem ExecutionReportReplaced.decode_agrees (record : ExecutionReportReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplaced.decode tokens = some record := by
  have distinct : ExecutionReportReplaced.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have workingPrice := readOptional_part [57, 54, 57, 48] record.workingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have preventedTradePx := readOptional_part [55, 57, 48, 51] record.preventedTradePx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have preventedTradeQty := readOptional_part [55, 57, 48, 52] record.preventedTradeQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have preventedTradeLiquidityIndicator := readOptional_part [55, 57, 48, 53] record.preventedTradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportReplaced.decode, origClOrdID, secondaryOrderID, workingPrice, preventedTradePx, preventedTradeQty, preventedTradeLiquidityIndicator, some_bind] <;> rfl

structure ExecutionReportRejected where
  ordRejReason : Option (Terminated 1)  -- tag 103
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[49, 48, 51]], [[53, 56]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { ordRejReason, text }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, ordRejReason, text, some_bind] <;> rfl

structure ExecutionReportRestated where
  execRestatementReason : Option (Terminated 1)  -- tag 378
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  workingPrice : Option (Terminated 1)  -- tag 9690

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [57, 54, 57, 48] record.workingPrice]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]], [[49, 57, 56]], [[57, 54, 57, 48]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let workingPrice ← readOptional [57, 54, 57, 48] tokens
  pure { execRestatementReason, secondaryOrderID, workingPrice }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have workingPrice := readOptional_part [57, 54, 57, 48] record.workingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, execRestatementReason, secondaryOrderID, workingPrice, some_bind] <;> rfl

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

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

structure NoSides where
  side : Terminated 1  -- tag 54
  clOrdID : Option (Terminated 1)  -- tag 11
  orderId : Option (Terminated 1)  -- tag 37
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 47
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  noPartyIDs : List NoPartyIDs  -- tag 453
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSaleNakedQty : Option (Terminated 1)  -- tag 6803
  shortSaleCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSaleLongQty : Option (Terminated 1)  -- tag 6805
  originOfTrans : Option (Terminated 1)  -- tag 8138
  intermediaryID : Option (Terminated 1)  -- tag 8139
  directedWholesaleIndic : Option (Terminated 1)  -- tag 8140
  feeCode : Option (Terminated 1)  -- tag 9882

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderId,
   Part.optional [49] record.account,
   Part.optional [52, 55] record.orderCapacity,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSaleNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSaleCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSaleLongQty,
   Part.optional [56, 49, 51, 56] record.originOfTrans,
   Part.optional [56, 49, 51, 57] record.intermediaryID,
   Part.optional [56, 49, 52, 48] record.directedWholesaleIndic,
   Part.optional [57, 56, 56, 50] record.feeCode]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 49]], [[51, 55]], [[49]], [[52, 55]], [[52, 51, 57]], [[52, 52, 48]], [52, 53, 51] :: NoPartyIDs.members, [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[57, 56, 56, 50]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [52, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSaleNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSaleCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSaleLongQty ← readOptional [54, 56, 48, 53] tokens
  let originOfTrans ← readOptional [56, 49, 51, 56] tokens
  let intermediaryID ← readOptional [56, 49, 51, 57] tokens
  let directedWholesaleIndic ← readOptional [56, 49, 52, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { side, clOrdID, orderId, account, orderCapacity, clearingFirm, clearingAccount, noPartyIDs, clientCrossRef, shortSaleNakedQty, shortSaleCoveredQty, shortSaleLongQty, originOfTrans, intermediaryID, directedWholesaleIndic, feeCode }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderCapacity := readOptional_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have shortSaleNakedQty := readOptional_part [54, 56, 48, 51] record.shortSaleNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have shortSaleCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSaleCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have shortSaleLongQty := readOptional_part [54, 56, 48, 53] record.shortSaleLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NoSides.decode, side, clOrdID, orderId, account, orderCapacity, clearingFirm, clearingAccount, noPartyIDs, clientCrossRef, shortSaleNakedQty, shortSaleCoveredQty, shortSaleLongQty, originOfTrans, intermediaryID, directedWholesaleIndic, feeCode, some_bind] <;> rfl

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

structure TradeCaptureReportAck where
  possResend : Option (Terminated 1)  -- tag 97
  transactTime : Terminated 1  -- tag 60
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  symbol : Terminated 1  -- tag 55
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Terminated 1  -- tag 150
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  noSides : List NoSides  -- tag 552
  tradeReportID : Terminated 1  -- tag 571
  tradeLinkID : Option (Terminated 1)  -- tag 820
  tradeReportType : Terminated 1  -- tag 856
  trdRptStatus : Terminated 1  -- tag 939
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Terminated 1  -- tag 1123
  execVenue : Option (Terminated 1)  -- tag 4805
  t1Settlement : Option (Terminated 1)  -- tag 8080
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  offExchTradeReportType : Terminated 1  -- tag 8181

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [53, 53] record.symbol,
   Part.optional [55, 53] record.tradeDate,
   Part.required [49, 53, 48] record.execType,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [56, 50, 48] record.tradeLinkID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [57, 51, 57] record.trdRptStatus,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [52, 56, 48, 53] record.execVenue,
   Part.optional [56, 48, 56, 48] record.t1Settlement,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.required [56, 49, 56, 49] record.offExchTradeReportType]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[54, 48]], [[51, 49]], [[51, 50]], [[53, 53]], [[55, 53]], [[49, 53, 48]], [[52, 56, 55]], [53, 53, 50] :: NoSides.members, [[53, 55, 49]], [[56, 50, 48]], [[56, 53, 54]], [[57, 51, 57]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[52, 56, 48, 53]], [[56, 48, 56, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 49]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let possResend ← readOptional [57, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeLinkID ← readOptional [56, 50, 48] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let trdRptStatus ← readRequired [57, 51, 57] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let execVenue ← readOptional [52, 56, 48, 53] tokens
  let t1Settlement ← readOptional [56, 48, 56, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let offExchTradeReportType ← readRequired [56, 49, 56, 49] tokens
  pure { possResend, transactTime, lastPx, lastShares, symbol, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeLinkID, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, execVenue, t1Settlement, removeCrossingFromClearing, offExchTradeReportType }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeLinkID := readOptional_part [56, 50, 48] record.tradeLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have trdRptStatus := readRequired_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execVenue := readOptional_part [52, 56, 48, 53] record.execVenue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have t1Settlement := readOptional_part [56, 48, 56, 48] record.t1Settlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have offExchTradeReportType := readRequired_part [56, 49, 56, 49] record.offExchTradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, possResend, transactTime, lastPx, lastShares, symbol, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeLinkID, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, execVenue, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, some_bind] <;> rfl

structure TradeCaptureReport where
  possResend : Option (Terminated 1)  -- tag 97
  transactTime : Terminated 1  -- tag 60
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  settlmntTyp : Option (Terminated 1)  -- tag 63
  futSettDate : Option (Terminated 1)  -- tag 64
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Terminated 1  -- tag 150
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  noSides : List NoSides  -- tag 552
  tradeReportID : Terminated 1  -- tag 571
  tradeReportRefID : Terminated 1  -- tag 572
  tradeLinkID : Option (Terminated 1)  -- tag 820
  tradeReportType : Terminated 1  -- tag 856
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Terminated 1  -- tag 1123
  execVenue : Option (Terminated 1)  -- tag 4805
  transactID : Terminated 1  -- tag 6807
  t1Settlement : Option (Terminated 1)  -- tag 8080
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  offExchTradeReportType : Terminated 1  -- tag 8181
  origCompID : Terminated 1  -- tag 9688
  origSubID : Terminated 1  -- tag 9689

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 52] record.futSettDate,
   Part.optional [55, 53] record.tradeDate,
   Part.required [49, 53, 48] record.execType,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.required [53, 55, 50] record.tradeReportRefID,
   Part.optional [56, 50, 48] record.tradeLinkID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [52, 56, 48, 53] record.execVenue,
   Part.required [54, 56, 48, 55] record.transactID,
   Part.optional [56, 48, 56, 48] record.t1Settlement,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.required [56, 49, 56, 49] record.offExchTradeReportType,
   Part.required [57, 54, 56, 56] record.origCompID,
   Part.required [57, 54, 56, 57] record.origSubID]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[54, 48]], [[51, 49]], [[51, 50]], [[53, 53]], [[53, 56]], [[54, 51]], [[54, 52]], [[55, 53]], [[49, 53, 48]], [[52, 56, 55]], [53, 53, 50] :: NoSides.members, [[53, 55, 49]], [[53, 55, 50]], [[56, 50, 48]], [[56, 53, 54]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[52, 56, 48, 53]], [[54, 56, 48, 55]], [[56, 48, 56, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 49]], [[57, 54, 56, 56]], [[57, 54, 56, 57]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let possResend ← readOptional [57, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let futSettDate ← readOptional [54, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportRefID ← readRequired [53, 55, 50] tokens
  let tradeLinkID ← readOptional [56, 50, 48] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let execVenue ← readOptional [52, 56, 48, 53] tokens
  let transactID ← readRequired [54, 56, 48, 55] tokens
  let t1Settlement ← readOptional [56, 48, 56, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let offExchTradeReportType ← readRequired [56, 49, 56, 49] tokens
  let origCompID ← readRequired [57, 54, 56, 56] tokens
  let origSubID ← readRequired [57, 54, 56, 57] tokens
  pure { possResend, transactTime, lastPx, lastShares, symbol, text, settlmntTyp, futSettDate, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeReportRefID, tradeLinkID, tradeReportType, tradeID, tradeHandlingInstr, execVenue, transactID, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, origCompID, origSubID }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have futSettDate := readOptional_part [54, 52] record.futSettDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeReportRefID := readRequired_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeLinkID := readOptional_part [56, 50, 48] record.tradeLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have execVenue := readOptional_part [52, 56, 48, 53] record.execVenue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have transactID := readRequired_part [54, 56, 48, 55] record.transactID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have t1Settlement := readOptional_part [56, 48, 56, 48] record.t1Settlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have offExchTradeReportType := readRequired_part [56, 49, 56, 49] record.offExchTradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have origCompID := readRequired_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have origSubID := readRequired_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, possResend, transactTime, lastPx, lastShares, symbol, text, settlmntTyp, futSettDate, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeReportRefID, tradeLinkID, tradeReportType, tradeID, tradeHandlingInstr, execVenue, transactID, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, origCompID, origSubID, some_bind] <;> rfl

inductive Message where
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportDoneForDay (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportDoneForDay)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)

def Message.tokens : Message → List Token
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportDoneForDay header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0

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
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCxaequitiesDropcopyFixV10Exchange
