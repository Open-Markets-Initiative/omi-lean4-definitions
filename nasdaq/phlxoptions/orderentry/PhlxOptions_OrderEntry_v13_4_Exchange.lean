import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Order Entry v13.4, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqPhlxoptionsOrderentryFixV134Exchange

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

structure AllocationAck where
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  allocID : Terminated 1  -- tag 70
  allocStatus : Terminated 1  -- tag 87
  allocRejCode : Option (Terminated 1)  -- tag 88

def AllocationAck.parts (record : AllocationAck) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 48] record.allocID,
   Part.required [56, 55] record.allocStatus,
   Part.optional [56, 56] record.allocRejCode]

def AllocationAck.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[54, 48]], [[55, 48]], [[56, 55]], [[56, 56]]]

theorem AllocationAck.shape (record : AllocationAck) : record.parts.map Part.tags = AllocationAck.tags := rfl

def AllocationAck.decode (tokens : List Token) : Option AllocationAck := do
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let allocID ← readRequired [55, 48] tokens
  let allocStatus ← readRequired [56, 55] tokens
  let allocRejCode ← readOptional [56, 56] tokens
  pure { text, transactTime, allocID, allocStatus, allocRejCode }

theorem AllocationAck.decode_agrees (record : AllocationAck) (tokens : List Token)
    (agrees : ∀ tags ∈ AllocationAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    AllocationAck.decode tokens = some record := by
  have distinct : AllocationAck.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have allocStatus := readRequired_part [56, 55] record.allocStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have allocRejCode := readOptional_part [56, 56] record.allocRejCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [AllocationAck.decode, text, transactTime, allocID, allocStatus, allocRejCode, some_bind] <;> rfl

structure BusinessMessageReject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refMsgType : Terminated 1  -- tag 372
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Terminated 1  -- tag 380

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [51, 56, 48] record.businessRejectReason]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 50]], [[51, 55, 57]], [[51, 56, 48]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  pure { refSeqNum, text, refMsgType, businessRejectRefID, businessRejectReason }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, text, refMsgType, businessRejectRefID, businessRejectReason, some_bind] <;> rfl

structure ExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdID : Option (Terminated 1)  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execRefID : Option (Terminated 1)  -- tag 19
  execTransType : Terminated 1  -- tag 20
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  rule80A : Option (Terminated 1)  -- tag 47
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Terminated 1  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  ordRejReason : Option (Terminated 1)  -- tag 103
  maxFloor : Option (Terminated 1)  -- tag 111
  execType : Terminated 1  -- tag 150
  leavesQty : Terminated 1  -- tag 151
  securityType : Terminated 1  -- tag 167
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  execRestatementReason : Option (Terminated 1)  -- tag 378
  dayOrderQty : Option (Terminated 1)  -- tag 424
  dayCumQty : Option (Terminated 1)  -- tag 425
  dayAvgPx : Option (Terminated 1)  -- tag 426
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multiLegReportingType : Option (Terminated 1)  -- tag 442
  maturityDate : Terminated 1  -- tag 541
  crossID : Option (Terminated 1)  -- tag 548
  workingIndicator : Option (Terminated 1)  -- tag 636
  legRefID : Option (Terminated 1)  -- tag 654
  underlyingPx : Option (Terminated 1)  -- tag 810
  underlyingQty : Option (Terminated 1)  -- tag 879
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  liquidityIndicator : Option (Terminated 1)  -- tag 9730
  auctionType : Option (Terminated 1)  -- tag 9373
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  auctionID : Option (Terminated 1)  -- tag 9370
  rFPID : Option (Terminated 1)  -- tag 9210
  displayWhen : Option (Terminated 1)  -- tag 1083
  displayRange : Option (Terminated 1)  -- tag 8020

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.optional [49, 49] record.clOrdID,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 57] record.execRefID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 48] record.lastMkt,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.rule80A,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.required [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 53, 48] record.execType,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 50, 52] record.dayOrderQty,
   Part.optional [52, 50, 53] record.dayCumQty,
   Part.optional [52, 50, 54] record.dayAvgPx,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [52, 52, 50] record.multiLegReportingType,
   Part.required [53, 52, 49] record.maturityDate,
   Part.optional [53, 52, 56] record.crossID,
   Part.optional [54, 51, 54] record.workingIndicator,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [56, 49, 48] record.underlyingPx,
   Part.optional [56, 55, 57] record.underlyingQty,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [57, 55, 51, 48] record.liquidityIndicator,
   Part.optional [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [57, 50, 49, 48] record.rFPID,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [56, 48, 50, 48] record.displayRange]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[49, 56]], [[49, 57]], [[50, 48]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 55]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[57, 57]], [[49, 48, 51]], [[49, 49, 49]], [[49, 53, 48]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[51, 55, 56]], [[52, 50, 52]], [[52, 50, 53]], [[52, 50, 54]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 52, 49]], [[53, 52, 56]], [[54, 51, 54]], [[54, 53, 52]], [[56, 49, 48]], [[56, 55, 57]], [[49, 48, 57, 50]], [[57, 55, 51, 48]], [[57, 51, 55, 51]], [[57, 48, 52, 51]], [[57, 48, 52, 52]], [[57, 48, 55, 54]], [[57, 51, 55, 48]], [[57, 50, 49, 48]], [[49, 48, 56, 51]], [[56, 48, 50, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execRefID ← readOptional [49, 57] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let rule80A ← readOptional [52, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let dayOrderQty ← readOptional [52, 50, 52] tokens
  let dayCumQty ← readOptional [52, 50, 53] tokens
  let dayAvgPx ← readOptional [52, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multiLegReportingType ← readOptional [52, 52, 50] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let crossID ← readOptional [53, 52, 56] tokens
  let workingIndicator ← readOptional [54, 51, 54] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let underlyingPx ← readOptional [56, 49, 48] tokens
  let underlyingQty ← readOptional [56, 55, 57] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let liquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let auctionType ← readOptional [57, 51, 55, 51] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let rFPID ← readOptional [57, 50, 49, 48] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  pure { account, avgPx, clOrdID, cumQty, execID, execInst, execRefID, execTransType, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, origClOrdID, price, rule80A, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, ordRejReason, maxFloor, execType, leavesQty, securityType, putOrCall, strikePrice, customerOrFirm, execRestatementReason, dayOrderQty, dayCumQty, dayAvgPx, expireDate, clearingFirm, clearingAccount, multiLegReportingType, maturityDate, crossID, workingIndicator, legRefID, underlyingPx, underlyingQty, priceProtectionScope, liquidityIndicator, auctionType, stepUpPriceType, stepUpPrice, stockLegGiveUp, auctionID, rFPID, displayWhen, displayRange }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have dayOrderQty := readOptional_part [52, 50, 52] record.dayOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have dayCumQty := readOptional_part [52, 50, 53] record.dayCumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have dayAvgPx := readOptional_part [52, 50, 54] record.dayAvgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have multiLegReportingType := readOptional_part [52, 52, 50] record.multiLegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have crossID := readOptional_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have workingIndicator := readOptional_part [54, 51, 54] record.workingIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have underlyingPx := readOptional_part [56, 49, 48] record.underlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have underlyingQty := readOptional_part [56, 55, 57] record.underlyingQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have liquidityIndicator := readOptional_part [57, 55, 51, 48] record.liquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have rFPID := readOptional_part [57, 50, 49, 48] record.rFPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  simp only [ExecutionReport.decode, account, avgPx, clOrdID, cumQty, execID, execInst, execRefID, execTransType, lastMkt, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, origClOrdID, price, rule80A, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, ordRejReason, maxFloor, execType, leavesQty, securityType, putOrCall, strikePrice, customerOrFirm, execRestatementReason, dayOrderQty, dayCumQty, dayAvgPx, expireDate, clearingFirm, clearingAccount, multiLegReportingType, maturityDate, crossID, workingIndicator, legRefID, underlyingPx, underlyingQty, priceProtectionScope, liquidityIndicator, auctionType, stepUpPriceType, stepUpPrice, stockLegGiveUp, auctionID, rFPID, displayWhen, displayRange, some_bind] <;> rfl

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

structure MemberKillSwitchResponse where
  text : Option (Terminated 1)  -- tag 58
  entitlementRequestID : Terminated 1  -- tag 1770
  noPartyEntitlements : List NoPartyEntitlements  -- tag 1772
  entitlementRequestResult : Option (Terminated 1)  -- tag 1881
  entitlementRequestStatus : Terminated 1  -- tag 1882

def MemberKillSwitchResponse.parts (record : MemberKillSwitchResponse) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.required [49, 55, 55, 48] record.entitlementRequestID,
   Part.group [49, 55, 55, 50] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within record.noPartyEntitlements,
   Part.optional [49, 56, 56, 49] record.entitlementRequestResult,
   Part.required [49, 56, 56, 50] record.entitlementRequestStatus]

def MemberKillSwitchResponse.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[49, 55, 55, 48]], [49, 55, 55, 50] :: NoPartyEntitlements.members, [[49, 56, 56, 49]], [[49, 56, 56, 50]]]

theorem MemberKillSwitchResponse.shape (record : MemberKillSwitchResponse) : record.parts.map Part.tags = MemberKillSwitchResponse.tags := rfl

def MemberKillSwitchResponse.decode (tokens : List Token) : Option MemberKillSwitchResponse := do
  let text ← readOptional [53, 56] tokens
  let entitlementRequestID ← readRequired [49, 55, 55, 48] tokens
  let noPartyEntitlements ← readGroup [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.decode tokens
  let entitlementRequestResult ← readOptional [49, 56, 56, 49] tokens
  let entitlementRequestStatus ← readRequired [49, 56, 56, 50] tokens
  pure { text, entitlementRequestID, noPartyEntitlements, entitlementRequestResult, entitlementRequestStatus }

theorem MemberKillSwitchResponse.decode_agrees (record : MemberKillSwitchResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ MemberKillSwitchResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MemberKillSwitchResponse.decode tokens = some record := by
  have distinct : MemberKillSwitchResponse.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have entitlementRequestID := readRequired_part [49, 55, 55, 48] record.entitlementRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyEntitlements := readGroup_part [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within NoPartyEntitlements.decode NoPartyEntitlements.decode_encode NoPartyEntitlements.led record.noPartyEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have entitlementRequestResult := readOptional_part [49, 56, 56, 49] record.entitlementRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have entitlementRequestStatus := readRequired_part [49, 56, 56, 50] record.entitlementRequestStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [MemberKillSwitchResponse.decode, text, entitlementRequestID, noPartyEntitlements, entitlementRequestResult, entitlementRequestStatus, some_bind] <;> rfl

structure MemberKillSwitchTriggerReset where
  transactTime : Terminated 1  -- tag 60
  noPartyEntitlements : List NoPartyEntitlements  -- tag 1772

def MemberKillSwitchTriggerReset.parts (record : MemberKillSwitchTriggerReset) : List Part :=
  [Part.required [54, 48] record.transactTime,
   Part.group [49, 55, 55, 50] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within record.noPartyEntitlements]

def MemberKillSwitchTriggerReset.tags : List (List (List UInt8)) :=
  [[[54, 48]], [49, 55, 55, 50] :: NoPartyEntitlements.members]

theorem MemberKillSwitchTriggerReset.shape (record : MemberKillSwitchTriggerReset) : record.parts.map Part.tags = MemberKillSwitchTriggerReset.tags := rfl

def MemberKillSwitchTriggerReset.decode (tokens : List Token) : Option MemberKillSwitchTriggerReset := do
  let transactTime ← readRequired [54, 48] tokens
  let noPartyEntitlements ← readGroup [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.decode tokens
  pure { transactTime, noPartyEntitlements }

theorem MemberKillSwitchTriggerReset.decode_agrees (record : MemberKillSwitchTriggerReset) (tokens : List Token)
    (agrees : ∀ tags ∈ MemberKillSwitchTriggerReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MemberKillSwitchTriggerReset.decode tokens = some record := by
  have distinct : MemberKillSwitchTriggerReset.tags.flatten.Nodup := by decide +kernel
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyEntitlements := readGroup_part [49, 55, 55, 50] [49, 51, 50, 52] NoPartyEntitlements.members NoPartyEntitlements.encode NoPartyEntitlements.within NoPartyEntitlements.decode NoPartyEntitlements.decode_encode NoPartyEntitlements.led record.noPartyEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [MemberKillSwitchTriggerReset.decode, transactTime, noPartyEntitlements, some_bind] <;> rfl

structure OrderCancelReject where
  orderID : Terminated 1  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58
  cxlRejResponseTo : Terminated 1  -- tag 434

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text,
   Part.required [52, 51, 52] record.cxlRejResponseTo]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[49, 48, 50]], [[53, 56]], [[52, 51, 52]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readRequired [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  pure { orderID, clOrdID, origClOrdID, ordStatus, cxlRejReason, text, cxlRejResponseTo }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, origClOrdID, ordStatus, cxlRejReason, text, cxlRejResponseTo, some_bind] <;> rfl

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

structure RequestForPrismNotification where
  rFPID : Terminated 1  -- tag 9210
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDate : Terminated 1  -- tag 541

def RequestForPrismNotification.parts (record : RequestForPrismNotification) : List Part :=
  [Part.required [57, 50, 49, 48] record.rFPID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [53, 52, 49] record.maturityDate]

def RequestForPrismNotification.tags : List (List (List UInt8)) :=
  [[[57, 50, 49, 48]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[53, 52, 49]]]

theorem RequestForPrismNotification.shape (record : RequestForPrismNotification) : record.parts.map Part.tags = RequestForPrismNotification.tags := rfl

def RequestForPrismNotification.decode (tokens : List Token) : Option RequestForPrismNotification := do
  let rFPID ← readRequired [57, 50, 49, 48] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  pure { rFPID, execInst, orderQty, ordType, price, side, symbol, securityType, putOrCall, strikePrice, customerOrFirm, maturityDate }

theorem RequestForPrismNotification.decode_agrees (record : RequestForPrismNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ RequestForPrismNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RequestForPrismNotification.decode tokens = some record := by
  have distinct : RequestForPrismNotification.tags.flatten.Nodup := by decide +kernel
  have rFPID := readRequired_part [57, 50, 49, 48] record.rFPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [RequestForPrismNotification.decode, rFPID, execInst, orderQty, ordType, price, side, symbol, securityType, putOrCall, strikePrice, customerOrFirm, maturityDate, some_bind] <;> rfl

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
  | allocationAck (header : Header) (r0 : AllocationAck)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | memberKillSwitchResponse (header : Header) (r0 : MemberKillSwitchResponse)
  | memberKillSwitchTriggerReset (header : Header) (r0 : MemberKillSwitchTriggerReset)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | reject (header : Header) (r0 : Reject)
  | requestForPrismNotification (header : Header) (r0 : RequestForPrismNotification)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .allocationAck header r0 => ⟨[51, 53], ⟨[80], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], ⟨[106], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .memberKillSwitchResponse header r0 => ⟨[51, 53], ⟨[85, 68, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .memberKillSwitchTriggerReset header r0 => ⟨[51, 53], ⟨[85, 68, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .requestForPrismNotification header r0 => ⟨[51, 53], ⟨[68, 83, 78], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [80] then
        if known (Header.tags ++ AllocationAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← AllocationAck.decode rest
          pure (.allocationAck header r0)
        else none
      else if token.value.val = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
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
      else if token.value.val = [85, 68, 66] then
        if known (Header.tags ++ MemberKillSwitchResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MemberKillSwitchResponse.decode rest
          pure (.memberKillSwitchResponse header r0)
        else none
      else if token.value.val = [85, 68, 67] then
        if known (Header.tags ++ MemberKillSwitchTriggerReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MemberKillSwitchTriggerReset.decode rest
          pure (.memberKillSwitchTriggerReset header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value.val = [68, 83, 78] then
        if known (Header.tags ++ RequestForPrismNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RequestForPrismNotification.decode rest
          pure (.requestForPrismNotification header r0)
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

theorem Message.decode_allocationAck (header : Header) (r0 : AllocationAck) :
    Message.decode (Message.tokens (.allocationAck header r0)) = some (.allocationAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (AllocationAck.tags) rfl rfl (by decide +kernel))
  have c1 := AllocationAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (AllocationAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ AllocationAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

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

theorem Message.decode_memberKillSwitchResponse (header : Header) (r0 : MemberKillSwitchResponse) :
    Message.decode (Message.tokens (.memberKillSwitchResponse header r0)) = some (.memberKillSwitchResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitchResponse.tags) rfl rfl (by decide +kernel))
  have c1 := MemberKillSwitchResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitchResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitchResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_memberKillSwitchTriggerReset (header : Header) (r0 : MemberKillSwitchTriggerReset) :
    Message.decode (Message.tokens (.memberKillSwitchTriggerReset header r0)) = some (.memberKillSwitchTriggerReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitchTriggerReset.tags) rfl rfl (by decide +kernel))
  have c1 := MemberKillSwitchTriggerReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitchTriggerReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitchTriggerReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_requestForPrismNotification (header : Header) (r0 : RequestForPrismNotification) :
    Message.decode (Message.tokens (.requestForPrismNotification header r0)) = some (.requestForPrismNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RequestForPrismNotification.tags) rfl rfl (by decide +kernel))
  have c1 := RequestForPrismNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RequestForPrismNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RequestForPrismNotification.tags) rfl
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
  | allocationAck header r0 => exact Message.decode_allocationAck header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | memberKillSwitchResponse header r0 => exact Message.decode_memberKillSwitchResponse header r0
  | memberKillSwitchTriggerReset header r0 => exact Message.decode_memberKillSwitchTriggerReset header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | reject header r0 => exact Message.decode_reject header r0
  | requestForPrismNotification header r0 => exact Message.decode_requestForPrismNotification header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_allocationAck (header : Header) (r0 : AllocationAck) :
    Message.decodeBytes (Message.encode (.allocationAck header r0)) = some (.allocationAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[80], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ AllocationAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocationAck header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[106], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

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

theorem Message.decodeBytes_memberKillSwitchResponse (header : Header) (r0 : MemberKillSwitchResponse) :
    Message.decodeBytes (Message.encode (.memberKillSwitchResponse header r0)) = some (.memberKillSwitchResponse header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitchResponse.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_memberKillSwitchResponse header r0

theorem Message.decodeBytes_memberKillSwitchTriggerReset (header : Header) (r0 : MemberKillSwitchTriggerReset) :
    Message.decodeBytes (Message.encode (.memberKillSwitchTriggerReset header r0)) = some (.memberKillSwitchTriggerReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitchTriggerReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_memberKillSwitchTriggerReset header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_requestForPrismNotification (header : Header) (r0 : RequestForPrismNotification) :
    Message.decodeBytes (Message.encode (.requestForPrismNotification header r0)) = some (.requestForPrismNotification header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68, 83, 78], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ RequestForPrismNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_requestForPrismNotification header r0

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
  | allocationAck header r0 => exact Message.decodeBytes_allocationAck header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | memberKillSwitchResponse header r0 => exact Message.decodeBytes_memberKillSwitchResponse header r0
  | memberKillSwitchTriggerReset header r0 => exact Message.decodeBytes_memberKillSwitchTriggerReset header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | requestForPrismNotification header r0 => exact Message.decodeBytes_requestForPrismNotification header r0
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

end Omi.NasdaqPhlxoptionsOrderentryFixV134Exchange
