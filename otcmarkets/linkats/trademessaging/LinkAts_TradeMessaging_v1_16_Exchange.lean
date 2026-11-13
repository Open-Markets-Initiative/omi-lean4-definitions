import Wire

/-!
# OTC Markets Group Trade Messaging v1.16, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.OtcmarketsLinkatsTrademessagingFixV116Exchange

structure Header where
  clOrdID : Option (Terminated 1)  -- tag 11
  msgSeqNum : Option (Terminated 1)  -- tag 34
  orderID : Option (Terminated 1)  -- tag 37
  senderCompID : Option (Terminated 1)  -- tag 49
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 52] record.msgSeqNum,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 52]], [[51, 55]], [[52, 57]], [[53, 50]], [[53, 54]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let clOrdID ← readOptional [49, 49] tokens
  let msgSeqNum ← readOptional [51, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { clOrdID, msgSeqNum, orderID, senderCompID, sendingTime, targetCompID, onBehalfOfCompID, onBehalfOfSubID, deliverToCompID, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have msgSeqNum := readOptional_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have senderCompID := readOptional_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Header.decode, clOrdID, msgSeqNum, orderID, senderCompID, sendingTime, targetCompID, onBehalfOfCompID, onBehalfOfSubID, deliverToCompID, deliverToSubID, some_bind] <;> rfl

structure ExecutionReport where
  counterOrdID : Option (Terminated 1)  -- tag 9552
  ordStatus : Option (Terminated 1)  -- tag 39
  leavesQty : Option (Terminated 1)  -- tag 151
  orderQty : Option (Terminated 1)  -- tag 38
  transactTime : Terminated 1  -- tag 60
  resultCode : Option (Terminated 1)  -- tag 9548
  text : Option (Terminated 1)  -- tag 58

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [57, 53, 53, 50] record.counterOrdID,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [51, 56] record.orderQty,
   Part.required [54, 48] record.transactTime,
   Part.optional [57, 53, 52, 56] record.resultCode,
   Part.optional [53, 56] record.text]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[57, 53, 53, 50]], [[51, 57]], [[49, 53, 49]], [[51, 56]], [[54, 48]], [[57, 53, 52, 56]], [[53, 56]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let counterOrdID ← readOptional [57, 53, 53, 50] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let orderQty ← readOptional [51, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let resultCode ← readOptional [57, 53, 52, 56] tokens
  let text ← readOptional [53, 56] tokens
  pure { counterOrdID, ordStatus, leavesQty, orderQty, transactTime, resultCode, text }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have counterOrdID := readOptional_part [57, 53, 53, 50] record.counterOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have resultCode := readOptional_part [57, 53, 52, 56] record.resultCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [ExecutionReport.decode, counterOrdID, ordStatus, leavesQty, orderQty, transactTime, resultCode, text, some_bind] <;> rfl

structure ExecutionReportNewTradeConfirm where
  liabilityFlag : Option (Terminated 1)  -- tag 9547
  orderQueuePosition : Option (Terminated 1)  -- tag 9551
  qAPRate : Option (Terminated 1)  -- tag 9665
  maxOrderID : Option (Terminated 1)  -- tag 9580

def ExecutionReportNewTradeConfirm.parts (record : ExecutionReportNewTradeConfirm) : List Part :=
  [Part.optional [57, 53, 52, 55] record.liabilityFlag,
   Part.optional [57, 53, 53, 49] record.orderQueuePosition,
   Part.optional [57, 54, 54, 53] record.qAPRate,
   Part.optional [57, 53, 56, 48] record.maxOrderID]

def ExecutionReportNewTradeConfirm.tags : List (List (List UInt8)) :=
  [[[57, 53, 52, 55]], [[57, 53, 53, 49]], [[57, 54, 54, 53]], [[57, 53, 56, 48]]]

theorem ExecutionReportNewTradeConfirm.shape (record : ExecutionReportNewTradeConfirm) : record.parts.map Part.tags = ExecutionReportNewTradeConfirm.tags := rfl

def ExecutionReportNewTradeConfirm.decode (tokens : List Token) : Option ExecutionReportNewTradeConfirm := do
  let liabilityFlag ← readOptional [57, 53, 52, 55] tokens
  let orderQueuePosition ← readOptional [57, 53, 53, 49] tokens
  let qAPRate ← readOptional [57, 54, 54, 53] tokens
  let maxOrderID ← readOptional [57, 53, 56, 48] tokens
  pure { liabilityFlag, orderQueuePosition, qAPRate, maxOrderID }

theorem ExecutionReportNewTradeConfirm.decode_agrees (record : ExecutionReportNewTradeConfirm) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportNewTradeConfirm.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportNewTradeConfirm.decode tokens = some record := by
  have distinct : ExecutionReportNewTradeConfirm.tags.flatten.Nodup := by decide +kernel
  have liabilityFlag := readOptional_part [57, 53, 52, 55] record.liabilityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQueuePosition := readOptional_part [57, 53, 53, 49] record.orderQueuePosition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have qAPRate := readOptional_part [57, 54, 54, 53] record.qAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have maxOrderID := readOptional_part [57, 53, 56, 48] record.maxOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [ExecutionReportNewTradeConfirm.decode, liabilityFlag, orderQueuePosition, qAPRate, maxOrderID, some_bind] <;> rfl

structure ExecutionReportPartialFill where
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  execID : Option (Terminated 1)  -- tag 17
  side : Terminated 1  -- tag 54
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  execInst : Option (Terminated 1)  -- tag 18
  solicitedFlag : Option (Terminated 1)  -- tag 9377
  orderCapacity : Option (Terminated 1)  -- tag 9528
  anonymous : Option (Terminated 1)  -- tag 9583
  qAPWaived : Option (Terminated 1)  -- tag 9666
  bFMMFlag : Option (Terminated 1)  -- tag 9710
  orderInitiatorFlag : Terminated 1  -- tag 9577
  counterPartySide : Option (Terminated 1)  -- tag 9592
  price : Terminated 1  -- tag 44
  qAPAmount : Terminated 1  -- tag 9664
  qAPRate : Terminated 1  -- tag 9665
  cumQty : Terminated 1  -- tag 14
  reportToExch : Terminated 1  -- tag 113
  counterPartyOrderCapacity : Option (Terminated 1)  -- tag 9593
  oATSReported : Terminated 1  -- tag 9581
  maxOrderID : Terminated 1  -- tag 9580
  mAXCumQty : Terminated 1  -- tag 9582
  insBidRcvd : Option (Terminated 1)  -- tag 9561
  insAskRcvd : Option (Terminated 1)  -- tag 9562
  insBidSizeRcvd : Option (Terminated 1)  -- tag 9563
  insAskSizeRcvd : Option (Terminated 1)  -- tag 9564
  receiverBid : Option (Terminated 1)  -- tag 9565
  receiverAsk : Option (Terminated 1)  -- tag 9566
  receiverBidSize : Option (Terminated 1)  -- tag 9567
  receiverAskSize : Option (Terminated 1)  -- tag 9568
  fillerBid : Option (Terminated 1)  -- tag 9569
  fillerAsk : Option (Terminated 1)  -- tag 9570
  fillerBidSize : Option (Terminated 1)  -- tag 9571
  fillerAskSize : Option (Terminated 1)  -- tag 9572
  insBidEx : Option (Terminated 1)  -- tag 9573
  insAskEx : Option (Terminated 1)  -- tag 9574
  insBidSizeEx : Option (Terminated 1)  -- tag 9575
  insAskSizeEx : Option (Terminated 1)  -- tag 9576

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [49, 55] record.execID,
   Part.required [53, 52] record.side,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 51, 55, 55] record.solicitedFlag,
   Part.optional [57, 53, 50, 56] record.orderCapacity,
   Part.optional [57, 53, 56, 51] record.anonymous,
   Part.optional [57, 54, 54, 54] record.qAPWaived,
   Part.optional [57, 55, 49, 48] record.bFMMFlag,
   Part.required [57, 53, 55, 55] record.orderInitiatorFlag,
   Part.optional [57, 53, 57, 50] record.counterPartySide,
   Part.required [52, 52] record.price,
   Part.required [57, 54, 54, 52] record.qAPAmount,
   Part.required [57, 54, 54, 53] record.qAPRate,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 49, 51] record.reportToExch,
   Part.optional [57, 53, 57, 51] record.counterPartyOrderCapacity,
   Part.required [57, 53, 56, 49] record.oATSReported,
   Part.required [57, 53, 56, 48] record.maxOrderID,
   Part.required [57, 53, 56, 50] record.mAXCumQty,
   Part.optional [57, 53, 54, 49] record.insBidRcvd,
   Part.optional [57, 53, 54, 50] record.insAskRcvd,
   Part.optional [57, 53, 54, 51] record.insBidSizeRcvd,
   Part.optional [57, 53, 54, 52] record.insAskSizeRcvd,
   Part.optional [57, 53, 54, 53] record.receiverBid,
   Part.optional [57, 53, 54, 54] record.receiverAsk,
   Part.optional [57, 53, 54, 55] record.receiverBidSize,
   Part.optional [57, 53, 54, 56] record.receiverAskSize,
   Part.optional [57, 53, 54, 57] record.fillerBid,
   Part.optional [57, 53, 55, 48] record.fillerAsk,
   Part.optional [57, 53, 55, 49] record.fillerBidSize,
   Part.optional [57, 53, 55, 50] record.fillerAskSize,
   Part.optional [57, 53, 55, 51] record.insBidEx,
   Part.optional [57, 53, 55, 52] record.insAskEx,
   Part.optional [57, 53, 55, 53] record.insBidSizeEx,
   Part.optional [57, 53, 55, 54] record.insAskSizeEx]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]], [[49, 55]], [[53, 52]], [[51, 50]], [[51, 49]], [[49, 56]], [[57, 51, 55, 55]], [[57, 53, 50, 56]], [[57, 53, 56, 51]], [[57, 54, 54, 54]], [[57, 55, 49, 48]], [[57, 53, 55, 55]], [[57, 53, 57, 50]], [[52, 52]], [[57, 54, 54, 52]], [[57, 54, 54, 53]], [[49, 52]], [[49, 49, 51]], [[57, 53, 57, 51]], [[57, 53, 56, 49]], [[57, 53, 56, 48]], [[57, 53, 56, 50]], [[57, 53, 54, 49]], [[57, 53, 54, 50]], [[57, 53, 54, 51]], [[57, 53, 54, 52]], [[57, 53, 54, 53]], [[57, 53, 54, 54]], [[57, 53, 54, 55]], [[57, 53, 54, 56]], [[57, 53, 54, 57]], [[57, 53, 55, 48]], [[57, 53, 55, 49]], [[57, 53, 55, 50]], [[57, 53, 55, 51]], [[57, 53, 55, 52]], [[57, 53, 55, 53]], [[57, 53, 55, 54]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let execID ← readOptional [49, 55] tokens
  let side ← readRequired [53, 52] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let solicitedFlag ← readOptional [57, 51, 55, 55] tokens
  let orderCapacity ← readOptional [57, 53, 50, 56] tokens
  let anonymous ← readOptional [57, 53, 56, 51] tokens
  let qAPWaived ← readOptional [57, 54, 54, 54] tokens
  let bFMMFlag ← readOptional [57, 55, 49, 48] tokens
  let orderInitiatorFlag ← readRequired [57, 53, 55, 55] tokens
  let counterPartySide ← readOptional [57, 53, 57, 50] tokens
  let price ← readRequired [52, 52] tokens
  let qAPAmount ← readRequired [57, 54, 54, 52] tokens
  let qAPRate ← readRequired [57, 54, 54, 53] tokens
  let cumQty ← readRequired [49, 52] tokens
  let reportToExch ← readRequired [49, 49, 51] tokens
  let counterPartyOrderCapacity ← readOptional [57, 53, 57, 51] tokens
  let oATSReported ← readRequired [57, 53, 56, 49] tokens
  let maxOrderID ← readRequired [57, 53, 56, 48] tokens
  let mAXCumQty ← readRequired [57, 53, 56, 50] tokens
  let insBidRcvd ← readOptional [57, 53, 54, 49] tokens
  let insAskRcvd ← readOptional [57, 53, 54, 50] tokens
  let insBidSizeRcvd ← readOptional [57, 53, 54, 51] tokens
  let insAskSizeRcvd ← readOptional [57, 53, 54, 52] tokens
  let receiverBid ← readOptional [57, 53, 54, 53] tokens
  let receiverAsk ← readOptional [57, 53, 54, 54] tokens
  let receiverBidSize ← readOptional [57, 53, 54, 55] tokens
  let receiverAskSize ← readOptional [57, 53, 54, 56] tokens
  let fillerBid ← readOptional [57, 53, 54, 57] tokens
  let fillerAsk ← readOptional [57, 53, 55, 48] tokens
  let fillerBidSize ← readOptional [57, 53, 55, 49] tokens
  let fillerAskSize ← readOptional [57, 53, 55, 50] tokens
  let insBidEx ← readOptional [57, 53, 55, 51] tokens
  let insAskEx ← readOptional [57, 53, 55, 52] tokens
  let insBidSizeEx ← readOptional [57, 53, 55, 53] tokens
  let insAskSizeEx ← readOptional [57, 53, 55, 54] tokens
  pure { symbol, symbolSfx, securityID, iDSource, execID, side, lastShares, lastPx, execInst, solicitedFlag, orderCapacity, anonymous, qAPWaived, bFMMFlag, orderInitiatorFlag, counterPartySide, price, qAPAmount, qAPRate, cumQty, reportToExch, counterPartyOrderCapacity, oATSReported, maxOrderID, mAXCumQty, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize, fillerBid, fillerAsk, fillerBidSize, fillerAskSize, insBidEx, insAskEx, insBidSizeEx, insAskSizeEx }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have solicitedFlag := readOptional_part [57, 51, 55, 55] record.solicitedFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderCapacity := readOptional_part [57, 53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have anonymous := readOptional_part [57, 53, 56, 51] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have qAPWaived := readOptional_part [57, 54, 54, 54] record.qAPWaived tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have bFMMFlag := readOptional_part [57, 55, 49, 48] record.bFMMFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderInitiatorFlag := readRequired_part [57, 53, 55, 55] record.orderInitiatorFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have counterPartySide := readOptional_part [57, 53, 57, 50] record.counterPartySide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have qAPAmount := readRequired_part [57, 54, 54, 52] record.qAPAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have qAPRate := readRequired_part [57, 54, 54, 53] record.qAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have reportToExch := readRequired_part [49, 49, 51] record.reportToExch tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have counterPartyOrderCapacity := readOptional_part [57, 53, 57, 51] record.counterPartyOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have oATSReported := readRequired_part [57, 53, 56, 49] record.oATSReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have maxOrderID := readRequired_part [57, 53, 56, 48] record.maxOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have mAXCumQty := readRequired_part [57, 53, 56, 50] record.mAXCumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have insBidRcvd := readOptional_part [57, 53, 54, 49] record.insBidRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have insAskRcvd := readOptional_part [57, 53, 54, 50] record.insAskRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have insBidSizeRcvd := readOptional_part [57, 53, 54, 51] record.insBidSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have insAskSizeRcvd := readOptional_part [57, 53, 54, 52] record.insAskSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have receiverBid := readOptional_part [57, 53, 54, 53] record.receiverBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have receiverAsk := readOptional_part [57, 53, 54, 54] record.receiverAsk tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have receiverBidSize := readOptional_part [57, 53, 54, 55] record.receiverBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have receiverAskSize := readOptional_part [57, 53, 54, 56] record.receiverAskSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have fillerBid := readOptional_part [57, 53, 54, 57] record.fillerBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have fillerAsk := readOptional_part [57, 53, 55, 48] record.fillerAsk tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have fillerBidSize := readOptional_part [57, 53, 55, 49] record.fillerBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have fillerAskSize := readOptional_part [57, 53, 55, 50] record.fillerAskSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have insBidEx := readOptional_part [57, 53, 55, 51] record.insBidEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have insAskEx := readOptional_part [57, 53, 55, 52] record.insAskEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have insBidSizeEx := readOptional_part [57, 53, 55, 53] record.insBidSizeEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have insAskSizeEx := readOptional_part [57, 53, 55, 54] record.insAskSizeEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, symbol, symbolSfx, securityID, iDSource, execID, side, lastShares, lastPx, execInst, solicitedFlag, orderCapacity, anonymous, qAPWaived, bFMMFlag, orderInitiatorFlag, counterPartySide, price, qAPAmount, qAPRate, cumQty, reportToExch, counterPartyOrderCapacity, oATSReported, maxOrderID, mAXCumQty, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize, fillerBid, fillerAsk, fillerBidSize, fillerAskSize, insBidEx, insAskEx, insBidSizeEx, insAskSizeEx, some_bind] <;> rfl

structure ExecutionReportFill where
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  execID : Option (Terminated 1)  -- tag 17
  side : Terminated 1  -- tag 54
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  execInst : Option (Terminated 1)  -- tag 18
  solicitedFlag : Option (Terminated 1)  -- tag 9377
  orderCapacity : Option (Terminated 1)  -- tag 9528
  anonymous : Option (Terminated 1)  -- tag 9583
  qAPWaived : Option (Terminated 1)  -- tag 9666
  bFMMFlag : Option (Terminated 1)  -- tag 9710
  orderInitiatorFlag : Terminated 1  -- tag 9577
  counterPartySide : Option (Terminated 1)  -- tag 9592
  price : Terminated 1  -- tag 44
  qAPAmount : Terminated 1  -- tag 9664
  qAPRate : Terminated 1  -- tag 9665
  cumQty : Terminated 1  -- tag 14
  reportToExch : Terminated 1  -- tag 113
  counterPartyOrderCapacity : Option (Terminated 1)  -- tag 9593
  oATSReported : Terminated 1  -- tag 9581
  maxOrderID : Terminated 1  -- tag 9580
  mAXCumQty : Terminated 1  -- tag 9582
  insBidRcvd : Option (Terminated 1)  -- tag 9561
  insAskRcvd : Option (Terminated 1)  -- tag 9562
  insBidSizeRcvd : Option (Terminated 1)  -- tag 9563
  insAskSizeRcvd : Option (Terminated 1)  -- tag 9564
  receiverBid : Option (Terminated 1)  -- tag 9565
  receiverAsk : Option (Terminated 1)  -- tag 9566
  receiverBidSize : Option (Terminated 1)  -- tag 9567
  receiverAskSize : Option (Terminated 1)  -- tag 9568
  fillerBid : Option (Terminated 1)  -- tag 9569
  fillerAsk : Option (Terminated 1)  -- tag 9570
  fillerBidSize : Option (Terminated 1)  -- tag 9571
  fillerAskSize : Option (Terminated 1)  -- tag 9572
  insBidEx : Option (Terminated 1)  -- tag 9573
  insAskEx : Option (Terminated 1)  -- tag 9574
  insBidSizeEx : Option (Terminated 1)  -- tag 9575
  insAskSizeEx : Option (Terminated 1)  -- tag 9576

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [49, 55] record.execID,
   Part.required [53, 52] record.side,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 51, 55, 55] record.solicitedFlag,
   Part.optional [57, 53, 50, 56] record.orderCapacity,
   Part.optional [57, 53, 56, 51] record.anonymous,
   Part.optional [57, 54, 54, 54] record.qAPWaived,
   Part.optional [57, 55, 49, 48] record.bFMMFlag,
   Part.required [57, 53, 55, 55] record.orderInitiatorFlag,
   Part.optional [57, 53, 57, 50] record.counterPartySide,
   Part.required [52, 52] record.price,
   Part.required [57, 54, 54, 52] record.qAPAmount,
   Part.required [57, 54, 54, 53] record.qAPRate,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 49, 51] record.reportToExch,
   Part.optional [57, 53, 57, 51] record.counterPartyOrderCapacity,
   Part.required [57, 53, 56, 49] record.oATSReported,
   Part.required [57, 53, 56, 48] record.maxOrderID,
   Part.required [57, 53, 56, 50] record.mAXCumQty,
   Part.optional [57, 53, 54, 49] record.insBidRcvd,
   Part.optional [57, 53, 54, 50] record.insAskRcvd,
   Part.optional [57, 53, 54, 51] record.insBidSizeRcvd,
   Part.optional [57, 53, 54, 52] record.insAskSizeRcvd,
   Part.optional [57, 53, 54, 53] record.receiverBid,
   Part.optional [57, 53, 54, 54] record.receiverAsk,
   Part.optional [57, 53, 54, 55] record.receiverBidSize,
   Part.optional [57, 53, 54, 56] record.receiverAskSize,
   Part.optional [57, 53, 54, 57] record.fillerBid,
   Part.optional [57, 53, 55, 48] record.fillerAsk,
   Part.optional [57, 53, 55, 49] record.fillerBidSize,
   Part.optional [57, 53, 55, 50] record.fillerAskSize,
   Part.optional [57, 53, 55, 51] record.insBidEx,
   Part.optional [57, 53, 55, 52] record.insAskEx,
   Part.optional [57, 53, 55, 53] record.insBidSizeEx,
   Part.optional [57, 53, 55, 54] record.insAskSizeEx]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]], [[49, 55]], [[53, 52]], [[51, 50]], [[51, 49]], [[49, 56]], [[57, 51, 55, 55]], [[57, 53, 50, 56]], [[57, 53, 56, 51]], [[57, 54, 54, 54]], [[57, 55, 49, 48]], [[57, 53, 55, 55]], [[57, 53, 57, 50]], [[52, 52]], [[57, 54, 54, 52]], [[57, 54, 54, 53]], [[49, 52]], [[49, 49, 51]], [[57, 53, 57, 51]], [[57, 53, 56, 49]], [[57, 53, 56, 48]], [[57, 53, 56, 50]], [[57, 53, 54, 49]], [[57, 53, 54, 50]], [[57, 53, 54, 51]], [[57, 53, 54, 52]], [[57, 53, 54, 53]], [[57, 53, 54, 54]], [[57, 53, 54, 55]], [[57, 53, 54, 56]], [[57, 53, 54, 57]], [[57, 53, 55, 48]], [[57, 53, 55, 49]], [[57, 53, 55, 50]], [[57, 53, 55, 51]], [[57, 53, 55, 52]], [[57, 53, 55, 53]], [[57, 53, 55, 54]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let execID ← readOptional [49, 55] tokens
  let side ← readRequired [53, 52] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let solicitedFlag ← readOptional [57, 51, 55, 55] tokens
  let orderCapacity ← readOptional [57, 53, 50, 56] tokens
  let anonymous ← readOptional [57, 53, 56, 51] tokens
  let qAPWaived ← readOptional [57, 54, 54, 54] tokens
  let bFMMFlag ← readOptional [57, 55, 49, 48] tokens
  let orderInitiatorFlag ← readRequired [57, 53, 55, 55] tokens
  let counterPartySide ← readOptional [57, 53, 57, 50] tokens
  let price ← readRequired [52, 52] tokens
  let qAPAmount ← readRequired [57, 54, 54, 52] tokens
  let qAPRate ← readRequired [57, 54, 54, 53] tokens
  let cumQty ← readRequired [49, 52] tokens
  let reportToExch ← readRequired [49, 49, 51] tokens
  let counterPartyOrderCapacity ← readOptional [57, 53, 57, 51] tokens
  let oATSReported ← readRequired [57, 53, 56, 49] tokens
  let maxOrderID ← readRequired [57, 53, 56, 48] tokens
  let mAXCumQty ← readRequired [57, 53, 56, 50] tokens
  let insBidRcvd ← readOptional [57, 53, 54, 49] tokens
  let insAskRcvd ← readOptional [57, 53, 54, 50] tokens
  let insBidSizeRcvd ← readOptional [57, 53, 54, 51] tokens
  let insAskSizeRcvd ← readOptional [57, 53, 54, 52] tokens
  let receiverBid ← readOptional [57, 53, 54, 53] tokens
  let receiverAsk ← readOptional [57, 53, 54, 54] tokens
  let receiverBidSize ← readOptional [57, 53, 54, 55] tokens
  let receiverAskSize ← readOptional [57, 53, 54, 56] tokens
  let fillerBid ← readOptional [57, 53, 54, 57] tokens
  let fillerAsk ← readOptional [57, 53, 55, 48] tokens
  let fillerBidSize ← readOptional [57, 53, 55, 49] tokens
  let fillerAskSize ← readOptional [57, 53, 55, 50] tokens
  let insBidEx ← readOptional [57, 53, 55, 51] tokens
  let insAskEx ← readOptional [57, 53, 55, 52] tokens
  let insBidSizeEx ← readOptional [57, 53, 55, 53] tokens
  let insAskSizeEx ← readOptional [57, 53, 55, 54] tokens
  pure { symbol, symbolSfx, securityID, iDSource, execID, side, lastShares, lastPx, execInst, solicitedFlag, orderCapacity, anonymous, qAPWaived, bFMMFlag, orderInitiatorFlag, counterPartySide, price, qAPAmount, qAPRate, cumQty, reportToExch, counterPartyOrderCapacity, oATSReported, maxOrderID, mAXCumQty, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize, fillerBid, fillerAsk, fillerBidSize, fillerAskSize, insBidEx, insAskEx, insBidSizeEx, insAskSizeEx }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have solicitedFlag := readOptional_part [57, 51, 55, 55] record.solicitedFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderCapacity := readOptional_part [57, 53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have anonymous := readOptional_part [57, 53, 56, 51] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have qAPWaived := readOptional_part [57, 54, 54, 54] record.qAPWaived tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have bFMMFlag := readOptional_part [57, 55, 49, 48] record.bFMMFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderInitiatorFlag := readRequired_part [57, 53, 55, 55] record.orderInitiatorFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have counterPartySide := readOptional_part [57, 53, 57, 50] record.counterPartySide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have qAPAmount := readRequired_part [57, 54, 54, 52] record.qAPAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have qAPRate := readRequired_part [57, 54, 54, 53] record.qAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have reportToExch := readRequired_part [49, 49, 51] record.reportToExch tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have counterPartyOrderCapacity := readOptional_part [57, 53, 57, 51] record.counterPartyOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have oATSReported := readRequired_part [57, 53, 56, 49] record.oATSReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have maxOrderID := readRequired_part [57, 53, 56, 48] record.maxOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have mAXCumQty := readRequired_part [57, 53, 56, 50] record.mAXCumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have insBidRcvd := readOptional_part [57, 53, 54, 49] record.insBidRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have insAskRcvd := readOptional_part [57, 53, 54, 50] record.insAskRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have insBidSizeRcvd := readOptional_part [57, 53, 54, 51] record.insBidSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have insAskSizeRcvd := readOptional_part [57, 53, 54, 52] record.insAskSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have receiverBid := readOptional_part [57, 53, 54, 53] record.receiverBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have receiverAsk := readOptional_part [57, 53, 54, 54] record.receiverAsk tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have receiverBidSize := readOptional_part [57, 53, 54, 55] record.receiverBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have receiverAskSize := readOptional_part [57, 53, 54, 56] record.receiverAskSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have fillerBid := readOptional_part [57, 53, 54, 57] record.fillerBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have fillerAsk := readOptional_part [57, 53, 55, 48] record.fillerAsk tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have fillerBidSize := readOptional_part [57, 53, 55, 49] record.fillerBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have fillerAskSize := readOptional_part [57, 53, 55, 50] record.fillerAskSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have insBidEx := readOptional_part [57, 53, 55, 51] record.insBidEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have insAskEx := readOptional_part [57, 53, 55, 52] record.insAskEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have insBidSizeEx := readOptional_part [57, 53, 55, 53] record.insBidSizeEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have insAskSizeEx := readOptional_part [57, 53, 55, 54] record.insAskSizeEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, symbol, symbolSfx, securityID, iDSource, execID, side, lastShares, lastPx, execInst, solicitedFlag, orderCapacity, anonymous, qAPWaived, bFMMFlag, orderInitiatorFlag, counterPartySide, price, qAPAmount, qAPRate, cumQty, reportToExch, counterPartyOrderCapacity, oATSReported, maxOrderID, mAXCumQty, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize, fillerBid, fillerAsk, fillerBidSize, fillerAskSize, insBidEx, insAskEx, insBidSizeEx, insAskSizeEx, some_bind] <;> rfl

structure ExecutionReportReplace where
  maxOrderID : Option (Terminated 1)  -- tag 9580
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22

def ExecutionReportReplace.parts (record : ExecutionReportReplace) : List Part :=
  [Part.optional [57, 53, 56, 48] record.maxOrderID,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource]

def ExecutionReportReplace.tags : List (List (List UInt8)) :=
  [[[57, 53, 56, 48]], [[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]]]

theorem ExecutionReportReplace.shape (record : ExecutionReportReplace) : record.parts.map Part.tags = ExecutionReportReplace.tags := rfl

def ExecutionReportReplace.decode (tokens : List Token) : Option ExecutionReportReplace := do
  let maxOrderID ← readOptional [57, 53, 56, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  pure { maxOrderID, symbol, symbolSfx, securityID, iDSource }

theorem ExecutionReportReplace.decode_agrees (record : ExecutionReportReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportReplace.decode tokens = some record := by
  have distinct : ExecutionReportReplace.tags.flatten.Nodup := by decide +kernel
  have maxOrderID := readOptional_part [57, 53, 56, 48] record.maxOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportReplace.decode, maxOrderID, symbol, symbolSfx, securityID, iDSource, some_bind] <;> rfl

structure ExecutionReportRejected where
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22

def ExecutionReportRejected.parts (record : ExecutionReportRejected) : List Part :=
  [Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource]

def ExecutionReportRejected.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]]]

theorem ExecutionReportRejected.shape (record : ExecutionReportRejected) : record.parts.map Part.tags = ExecutionReportRejected.tags := rfl

def ExecutionReportRejected.decode (tokens : List Token) : Option ExecutionReportRejected := do
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  pure { symbol, symbolSfx, securityID, iDSource }

theorem ExecutionReportRejected.decode_agrees (record : ExecutionReportRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejected.decode tokens = some record := by
  have distinct : ExecutionReportRejected.tags.flatten.Nodup := by decide +kernel
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [ExecutionReportRejected.decode, symbol, symbolSfx, securityID, iDSource, some_bind] <;> rfl

structure ExecutionReportCountered where
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  side : Option (Terminated 1)  -- tag 54
  price : Terminated 1  -- tag 44
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Option (Terminated 1)  -- tag 59
  duration : Option (Terminated 1)  -- tag 9559
  solicitedFlag : Option (Terminated 1)  -- tag 9377
  orderCapacity : Option (Terminated 1)  -- tag 9528
  bFMMFlag : Option (Terminated 1)  -- tag 9710
  counterState : Option (Terminated 1)  -- tag 9553
  counterPartyOrderCapacity : Option (Terminated 1)  -- tag 9593

def ExecutionReportCountered.parts (record : ExecutionReportCountered) : List Part :=
  [Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [53, 52] record.side,
   Part.required [52, 52] record.price,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 53, 53, 57] record.duration,
   Part.optional [57, 51, 55, 55] record.solicitedFlag,
   Part.optional [57, 53, 50, 56] record.orderCapacity,
   Part.optional [57, 55, 49, 48] record.bFMMFlag,
   Part.optional [57, 53, 53, 51] record.counterState,
   Part.optional [57, 53, 57, 51] record.counterPartyOrderCapacity]

def ExecutionReportCountered.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]], [[53, 52]], [[52, 52]], [[49, 56]], [[53, 57]], [[57, 53, 53, 57]], [[57, 51, 55, 55]], [[57, 53, 50, 56]], [[57, 55, 49, 48]], [[57, 53, 53, 51]], [[57, 53, 57, 51]]]

theorem ExecutionReportCountered.shape (record : ExecutionReportCountered) : record.parts.map Part.tags = ExecutionReportCountered.tags := rfl

def ExecutionReportCountered.decode (tokens : List Token) : Option ExecutionReportCountered := do
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let side ← readOptional [53, 52] tokens
  let price ← readRequired [52, 52] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let duration ← readOptional [57, 53, 53, 57] tokens
  let solicitedFlag ← readOptional [57, 51, 55, 55] tokens
  let orderCapacity ← readOptional [57, 53, 50, 56] tokens
  let bFMMFlag ← readOptional [57, 55, 49, 48] tokens
  let counterState ← readOptional [57, 53, 53, 51] tokens
  let counterPartyOrderCapacity ← readOptional [57, 53, 57, 51] tokens
  pure { symbol, symbolSfx, securityID, iDSource, side, price, execInst, timeInForce, duration, solicitedFlag, orderCapacity, bFMMFlag, counterState, counterPartyOrderCapacity }

theorem ExecutionReportCountered.decode_agrees (record : ExecutionReportCountered) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCountered.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCountered.decode tokens = some record := by
  have distinct : ExecutionReportCountered.tags.flatten.Nodup := by decide +kernel
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have duration := readOptional_part [57, 53, 53, 57] record.duration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have solicitedFlag := readOptional_part [57, 51, 55, 55] record.solicitedFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderCapacity := readOptional_part [57, 53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have bFMMFlag := readOptional_part [57, 55, 49, 48] record.bFMMFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have counterState := readOptional_part [57, 53, 53, 51] record.counterState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have counterPartyOrderCapacity := readOptional_part [57, 53, 57, 51] record.counterPartyOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [ExecutionReportCountered.decode, symbol, symbolSfx, securityID, iDSource, side, price, execInst, timeInForce, duration, solicitedFlag, orderCapacity, bFMMFlag, counterState, counterPartyOrderCapacity, some_bind] <;> rfl

structure CancelRejected where
  counterOrdID : Option (Terminated 1)  -- tag 9552
  transactTime : Terminated 1  -- tag 60
  resultCode : Terminated 1  -- tag 9548
  text : Terminated 1  -- tag 58

def CancelRejected.parts (record : CancelRejected) : List Part :=
  [Part.optional [57, 53, 53, 50] record.counterOrdID,
   Part.required [54, 48] record.transactTime,
   Part.required [57, 53, 52, 56] record.resultCode,
   Part.required [53, 56] record.text]

def CancelRejected.tags : List (List (List UInt8)) :=
  [[[57, 53, 53, 50]], [[54, 48]], [[57, 53, 52, 56]], [[53, 56]]]

theorem CancelRejected.shape (record : CancelRejected) : record.parts.map Part.tags = CancelRejected.tags := rfl

def CancelRejected.decode (tokens : List Token) : Option CancelRejected := do
  let counterOrdID ← readOptional [57, 53, 53, 50] tokens
  let transactTime ← readRequired [54, 48] tokens
  let resultCode ← readRequired [57, 53, 52, 56] tokens
  let text ← readRequired [53, 56] tokens
  pure { counterOrdID, transactTime, resultCode, text }

theorem CancelRejected.decode_agrees (record : CancelRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelRejected.decode tokens = some record := by
  have distinct : CancelRejected.tags.flatten.Nodup := by decide +kernel
  have counterOrdID := readOptional_part [57, 53, 53, 50] record.counterOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have resultCode := readRequired_part [57, 53, 52, 56] record.resultCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [CancelRejected.decode, counterOrdID, transactTime, resultCode, text, some_bind] <;> rfl

inductive Message where
  | executionReportNewTradeConfirm (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewTradeConfirm)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplace)
  | executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected)
  | executionReportCountered (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCountered)
  | cancelRejected (header : Header) (r0 : CancelRejected)

def Message.tokens : Message → List Token
  | .executionReportNewTradeConfirm header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportReplace header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejected header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .executionReportCountered header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts)
  | .cancelRejected header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewTradeConfirm.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportNewTradeConfirm.decode rest
              pure (.executionReportNewTradeConfirm header r0 r1)
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
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplace.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportReplace.decode rest
              pure (.executionReportReplace header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejected.decode rest
              pure (.executionReportRejected header r0 r1)
            else none
          else if key.val = [83] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCountered.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportCountered.decode rest
              pure (.executionReportCountered header r0 r1)
            else none
          else none
      else if token.value.val = [57] then
        if known (Header.tags ++ CancelRejected.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelRejected.decode rest
          pure (.cancelRejected header r0)
        else none
      else none
    else none

theorem Message.decode_executionReportNewTradeConfirm (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewTradeConfirm) :
    Message.decode (Message.tokens (.executionReportNewTradeConfirm header r0 r1)) = some (.executionReportNewTradeConfirm header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewTradeConfirm.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNewTradeConfirm.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNewTradeConfirm.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNewTradeConfirm.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNewTradeConfirm.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewTradeConfirm.tags) rfl
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

theorem Message.decode_executionReportReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplace) :
    Message.decode (Message.tokens (.executionReportReplace header r0 r1)) = some (.executionReportReplace header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplace.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportReplace.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportReplace.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportReplace.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplace.tags) rfl
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

theorem Message.decode_executionReportCountered (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCountered) :
    Message.decode (Message.tokens (.executionReportCountered header r0 r1)) = some (.executionReportCountered header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCountered.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportCountered.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[83], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[83], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportCountered.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCountered.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportCountered.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCountered.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_cancelRejected (header : Header) (r0 : CancelRejected) :
    Message.decode (Message.tokens (.cancelRejected header r0)) = some (.cancelRejected header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelRejected.tags) rfl rfl (by decide +kernel))
  have c1 := CancelRejected.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelRejected.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportNewTradeConfirm header r0 r1 => exact Message.decode_executionReportNewTradeConfirm header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportReplace header r0 r1 => exact Message.decode_executionReportReplace header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decode_executionReportRejected header r0 r1
  | executionReportCountered header r0 r1 => exact Message.decode_executionReportCountered header r0 r1
  | cancelRejected header r0 => exact Message.decode_cancelRejected header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportNewTradeConfirm (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNewTradeConfirm) :
    Message.decodeBytes (Message.encode (.executionReportNewTradeConfirm header r0 r1)) = some (.executionReportNewTradeConfirm header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNewTradeConfirm.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNewTradeConfirm header r0 r1

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

theorem Message.decodeBytes_executionReportReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplace) :
    Message.decodeBytes (Message.encode (.executionReportReplace header r0 r1)) = some (.executionReportReplace header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportReplace.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplace header r0 r1

theorem Message.decodeBytes_executionReportRejected (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejected) :
    Message.decodeBytes (Message.encode (.executionReportRejected header r0 r1)) = some (.executionReportRejected header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejected header r0 r1

theorem Message.decodeBytes_executionReportCountered (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCountered) :
    Message.decodeBytes (Message.encode (.executionReportCountered header r0 r1)) = some (.executionReportCountered header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCountered.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCountered header r0 r1

theorem Message.decodeBytes_cancelRejected (header : Header) (r0 : CancelRejected) :
    Message.decodeBytes (Message.encode (.cancelRejected header r0)) = some (.cancelRejected header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelRejected header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportNewTradeConfirm header r0 r1 => exact Message.decodeBytes_executionReportNewTradeConfirm header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportReplace header r0 r1 => exact Message.decodeBytes_executionReportReplace header r0 r1
  | executionReportRejected header r0 r1 => exact Message.decodeBytes_executionReportRejected header r0 r1
  | executionReportCountered header r0 r1 => exact Message.decodeBytes_executionReportCountered header r0 r1
  | cancelRejected header r0 => exact Message.decodeBytes_cancelRejected header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.OtcmarketsLinkatsTrademessagingFixV116Exchange
