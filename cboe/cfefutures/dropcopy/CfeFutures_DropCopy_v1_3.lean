import Wire

/-!
# Chicago Board Options Exchange Drop Copy v1.3

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCfefuturesDropcopyFixV13

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
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
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
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
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompId ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompID, onBehalfOfSubID, deliverToCompId, deliverToSubID }

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
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompId := readOptional_part [49, 50, 56] record.deliverToCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompID, onBehalfOfSubID, deliverToCompId, deliverToSubID, some_bind] <;> rfl

structure ExecutionReport where
  tradeDate : Option (Terminated 1)  -- tag 75
  execTransType : Option (Terminated 1)  -- tag 20
  execID : Option (Terminated 1)  -- tag 17
  secondaryExecID : Option (Terminated 1)  -- tag 527
  execRefID : Option (Terminated 1)  -- tag 19
  clOrdID : Option (Terminated 1)  -- tag 11
  orderId : Option (Terminated 1)  -- tag 37
  ordStatus : Option (Terminated 1)  -- tag 39
  account : Option (Terminated 1)  -- tag 1
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126
  minQty : Option (Terminated 1)  -- tag 110
  cMTANumber : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  symbol : Option (Terminated 1)  -- tag 55
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  securityDesc : Option (Terminated 1)  -- tag 107
  securityID : Option (Terminated 1)  -- tag 48
  senderLocationID : Option (Terminated 1)  -- tag 142
  securityType : Option (Terminated 1)  -- tag 167
  side : Option (Terminated 1)  -- tag 54
  orderQty : Option (Terminated 1)  -- tag 38
  dayOrderQty : Option (Terminated 1)  -- tag 424
  cumQty : Option (Terminated 1)  -- tag 14
  dayCumQty : Option (Terminated 1)  -- tag 425
  leavesQty : Option (Terminated 1)  -- tag 151
  price : Option (Terminated 1)  -- tag 44
  avgPx : Option (Terminated 1)  -- tag 6
  dayAvgPx : Option (Terminated 1)  -- tag 426
  stopPx : Option (Terminated 1)  -- tag 99
  secondaryOrderID : Option (Terminated 1)  -- tag 198
  tradeLiquidityIndicator : Option (Terminated 1)  -- tag 9730
  feeCode : Option (Terminated 1)  -- tag 9882
  modifySequence : Option (Terminated 1)  -- tag 9617
  origCompID : Option (Terminated 1)  -- tag 9688
  origSubID : Option (Terminated 1)  -- tag 9689
  transactTime : Option (Terminated 1)  -- tag 60
  cTICode : Option (Terminated 1)  -- tag 9702
  orderCapacity : Option (Terminated 1)  -- tag 47
  openClose : Option (Terminated 1)  -- tag 77
  custOrderHandlingInst : Option (Terminated 1)  -- tag 1031

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [55, 53] record.tradeDate,
   Part.optional [50, 48] record.execTransType,
   Part.optional [49, 55] record.execID,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [49, 57] record.execRefID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderId,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [49] record.account,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [52, 51, 57] record.cMTANumber,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [52, 56] record.securityID,
   Part.optional [49, 52, 50] record.senderLocationID,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 52] record.side,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 50, 52] record.dayOrderQty,
   Part.optional [49, 52] record.cumQty,
   Part.optional [52, 50, 53] record.dayCumQty,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [52, 52] record.price,
   Part.optional [54] record.avgPx,
   Part.optional [52, 50, 54] record.dayAvgPx,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 57, 56] record.secondaryOrderID,
   Part.optional [57, 55, 51, 48] record.tradeLiquidityIndicator,
   Part.optional [57, 56, 56, 50] record.feeCode,
   Part.optional [57, 54, 49, 55] record.modifySequence,
   Part.optional [57, 54, 56, 56] record.origCompID,
   Part.optional [57, 54, 56, 57] record.origSubID,
   Part.optional [54, 48] record.transactTime,
   Part.optional [57, 55, 48, 50] record.cTICode,
   Part.optional [52, 55] record.orderCapacity,
   Part.optional [55, 55] record.openClose,
   Part.optional [49, 48, 51, 49] record.custOrderHandlingInst]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[55, 53]], [[50, 48]], [[49, 55]], [[53, 50, 55]], [[49, 57]], [[49, 49]], [[51, 55]], [[51, 57]], [[49]], [[53, 57]], [[49, 50, 54]], [[49, 49, 48]], [[52, 51, 57]], [[52, 52, 48]], [[53, 53]], [[50, 48, 48]], [[50, 48, 53]], [[49, 48, 55]], [[52, 56]], [[49, 52, 50]], [[49, 54, 55]], [[53, 52]], [[51, 56]], [[52, 50, 52]], [[49, 52]], [[52, 50, 53]], [[49, 53, 49]], [[52, 52]], [[54]], [[52, 50, 54]], [[57, 57]], [[49, 57, 56]], [[57, 55, 51, 48]], [[57, 56, 56, 50]], [[57, 54, 49, 55]], [[57, 54, 56, 56]], [[57, 54, 56, 57]], [[54, 48]], [[57, 55, 48, 50]], [[52, 55]], [[55, 55]], [[49, 48, 51, 49]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let tradeDate ← readOptional [55, 53] tokens
  let execTransType ← readOptional [50, 48] tokens
  let execID ← readOptional [49, 55] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let execRefID ← readOptional [49, 57] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let account ← readOptional [49] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let cMTANumber ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let securityID ← readOptional [52, 56] tokens
  let senderLocationID ← readOptional [49, 52, 50] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readOptional [51, 56] tokens
  let dayOrderQty ← readOptional [52, 50, 52] tokens
  let cumQty ← readOptional [49, 52] tokens
  let dayCumQty ← readOptional [52, 50, 53] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let price ← readOptional [52, 52] tokens
  let avgPx ← readOptional [54] tokens
  let dayAvgPx ← readOptional [52, 50, 54] tokens
  let stopPx ← readOptional [57, 57] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  let tradeLiquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  let modifySequence ← readOptional [57, 54, 49, 55] tokens
  let origCompID ← readOptional [57, 54, 56, 56] tokens
  let origSubID ← readOptional [57, 54, 56, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let cTICode ← readOptional [57, 55, 48, 50] tokens
  let orderCapacity ← readOptional [52, 55] tokens
  let openClose ← readOptional [55, 55] tokens
  let custOrderHandlingInst ← readOptional [49, 48, 51, 49] tokens
  pure { tradeDate, execTransType, execID, secondaryExecID, execRefID, clOrdID, orderId, ordStatus, account, timeInForce, expireTime, minQty, cMTANumber, clearingAccount, symbol, maturityMonth, maturityDay, securityDesc, securityID, senderLocationID, securityType, side, orderQty, dayOrderQty, cumQty, dayCumQty, leavesQty, price, avgPx, dayAvgPx, stopPx, secondaryOrderID, tradeLiquidityIndicator, feeCode, modifySequence, origCompID, origSubID, transactTime, cTICode, orderCapacity, openClose, custOrderHandlingInst }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have cMTANumber := readOptional_part [52, 51, 57] record.cMTANumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have senderLocationID := readOptional_part [49, 52, 50] record.senderLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have dayOrderQty := readOptional_part [52, 50, 52] record.dayOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have dayCumQty := readOptional_part [52, 50, 53] record.dayCumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have dayAvgPx := readOptional_part [52, 50, 54] record.dayAvgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have tradeLiquidityIndicator := readOptional_part [57, 55, 51, 48] record.tradeLiquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have modifySequence := readOptional_part [57, 54, 49, 55] record.modifySequence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have origCompID := readOptional_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have origSubID := readOptional_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have cTICode := readOptional_part [57, 55, 48, 50] record.cTICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have orderCapacity := readOptional_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have custOrderHandlingInst := readOptional_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  simp only [ExecutionReport.decode, tradeDate, execTransType, execID, secondaryExecID, execRefID, clOrdID, orderId, ordStatus, account, timeInForce, expireTime, minQty, cMTANumber, clearingAccount, symbol, maturityMonth, maturityDay, securityDesc, securityID, senderLocationID, securityType, side, orderQty, dayOrderQty, cumQty, dayCumQty, leavesQty, price, avgPx, dayAvgPx, stopPx, secondaryOrderID, tradeLiquidityIndicator, feeCode, modifySequence, origCompID, origSubID, transactTime, cTICode, orderCapacity, openClose, custOrderHandlingInst, some_bind] <;> rfl

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
  trdType : Option (Terminated 1)  -- tag 828
  noContraBrokers : Option (Terminated 1)  -- tag 382
  contraBroker : Option (Terminated 1)  -- tag 375
  lastShares : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  multilegReportingType : Option (Terminated 1)  -- tag 442

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.optional [56, 50, 56] record.trdType,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 49] record.lastPx,
   Part.optional [52, 52, 50] record.multilegReportingType]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[56, 50, 56]], [[51, 56, 50]], [[51, 55, 53]], [[51, 50]], [[51, 49]], [[52, 52, 50]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let trdType ← readOptional [56, 50, 56] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let lastShares ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let multilegReportingType ← readOptional [52, 52, 50] tokens
  pure { trdType, noContraBrokers, contraBroker, lastShares, lastPx, multilegReportingType }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have multilegReportingType := readOptional_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, trdType, noContraBrokers, contraBroker, lastShares, lastPx, multilegReportingType, some_bind] <;> rfl

structure ExecutionReportFill where
  trdType : Option (Terminated 1)  -- tag 828
  noContraBrokers : Option (Terminated 1)  -- tag 382
  contraBroker : Option (Terminated 1)  -- tag 375
  lastShares : Option (Terminated 1)  -- tag 32
  lastPx : Option (Terminated 1)  -- tag 31
  multilegReportingType : Option (Terminated 1)  -- tag 442

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.optional [56, 50, 56] record.trdType,
   Part.optional [51, 56, 50] record.noContraBrokers,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [51, 50] record.lastShares,
   Part.optional [51, 49] record.lastPx,
   Part.optional [52, 52, 50] record.multilegReportingType]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[56, 50, 56]], [[51, 56, 50]], [[51, 55, 53]], [[51, 50]], [[51, 49]], [[52, 52, 50]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let trdType ← readOptional [56, 50, 56] tokens
  let noContraBrokers ← readOptional [51, 56, 50] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let lastShares ← readOptional [51, 50] tokens
  let lastPx ← readOptional [51, 49] tokens
  let multilegReportingType ← readOptional [52, 52, 50] tokens
  pure { trdType, noContraBrokers, contraBroker, lastShares, lastPx, multilegReportingType }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noContraBrokers := readOptional_part [51, 56, 50] record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have multilegReportingType := readOptional_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, trdType, noContraBrokers, contraBroker, lastShares, lastPx, multilegReportingType, some_bind] <;> rfl

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
  clearingPrice : Option (Terminated 1)  -- tag 21050
  clearingSymbol : Option (Terminated 1)  -- tag 21053

def ExecutionReportRestated.parts (record : ExecutionReportRestated) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [50, 49, 48, 53, 48] record.clearingPrice,
   Part.optional [50, 49, 48, 53, 51] record.clearingSymbol]

def ExecutionReportRestated.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]], [[50, 49, 48, 53, 48]], [[50, 49, 48, 53, 51]]]

theorem ExecutionReportRestated.shape (record : ExecutionReportRestated) : record.parts.map Part.tags = ExecutionReportRestated.tags := rfl

def ExecutionReportRestated.decode (tokens : List Token) : Option ExecutionReportRestated := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let clearingPrice ← readOptional [50, 49, 48, 53, 48] tokens
  let clearingSymbol ← readOptional [50, 49, 48, 53, 51] tokens
  pure { execRestatementReason, clearingPrice, clearingSymbol }

theorem ExecutionReportRestated.decode_agrees (record : ExecutionReportRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRestated.decode tokens = some record := by
  have distinct : ExecutionReportRestated.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clearingPrice := readOptional_part [50, 49, 48, 53, 48] record.clearingPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clearingSymbol := readOptional_part [50, 49, 48, 53, 51] record.clearingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportRestated.decode, execRestatementReason, clearingPrice, clearingSymbol, some_bind] <;> rfl

structure ExecutionReportMassCancelComplete where
  massCancelID : Option (Terminated 1)  -- tag 7695
  cancelledOrderCount : Option (Terminated 1)  -- tag 7696

def ExecutionReportMassCancelComplete.parts (record : ExecutionReportMassCancelComplete) : List Part :=
  [Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.optional [55, 54, 57, 54] record.cancelledOrderCount]

def ExecutionReportMassCancelComplete.tags : List (List (List UInt8)) :=
  [[[55, 54, 57, 53]], [[55, 54, 57, 54]]]

theorem ExecutionReportMassCancelComplete.shape (record : ExecutionReportMassCancelComplete) : record.parts.map Part.tags = ExecutionReportMassCancelComplete.tags := rfl

def ExecutionReportMassCancelComplete.decode (tokens : List Token) : Option ExecutionReportMassCancelComplete := do
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let cancelledOrderCount ← readOptional [55, 54, 57, 54] tokens
  pure { massCancelID, cancelledOrderCount }

theorem ExecutionReportMassCancelComplete.decode_agrees (record : ExecutionReportMassCancelComplete) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportMassCancelComplete.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportMassCancelComplete.decode tokens = some record := by
  have distinct : ExecutionReportMassCancelComplete.tags.flatten.Nodup := by decide +kernel
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have cancelledOrderCount := readOptional_part [55, 54, 57, 54] record.cancelledOrderCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportMassCancelComplete.decode, massCancelID, cancelledOrderCount, some_bind] <;> rfl

inductive Message where
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportRestated (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRestated)
  | executionReportMassCancelComplete (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportMassCancelComplete)

def Message.tokens : Message → List Token
  | .executionReportNew header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportRestated header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r1.parts)
  | .executionReportMassCancelComplete header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts)

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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decode_executionReportRestated header r0 r1
  | executionReportMassCancelComplete header r0 r1 => exact Message.decode_executionReportMassCancelComplete header r0 r1

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportRestated header r0 r1 => exact Message.decodeBytes_executionReportRestated header r0 r1
  | executionReportMassCancelComplete header r0 r1 => exact Message.decodeBytes_executionReportMassCancelComplete header r0 r1

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCfefuturesDropcopyFixV13
