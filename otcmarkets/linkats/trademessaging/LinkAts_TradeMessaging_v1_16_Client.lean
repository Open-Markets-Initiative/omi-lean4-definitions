import Wire

/-!
# OTC Markets Group Trade Messaging v1.16, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.OtcmarketsLinkatsTrademessagingFixV116Client

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

structure NewTrade where
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  ordType : Terminated 1  -- tag 40
  side : Terminated 1  -- tag 54
  price : Terminated 1  -- tag 44
  orderQty : Terminated 1  -- tag 38
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Option (Terminated 1)  -- tag 59
  duration : Option (Terminated 1)  -- tag 9559
  solicitedFlag : Option (Terminated 1)  -- tag 9377
  orderCapacity : Option (Terminated 1)  -- tag 9528
  pingECN : Option (Terminated 1)  -- tag 9600
  bFMMFlag : Option (Terminated 1)  -- tag 9710
  counterOrdID : Option (Terminated 1)  -- tag 9552
  transactTime : Terminated 1  -- tag 60
  qAPRate : Terminated 1  -- tag 9665
  liabilityFlag : Terminated 1  -- tag 9547
  orderQueuePosition : Terminated 1  -- tag 9551
  restrictToRoundLots : Option (Terminated 1)  -- tag 9549
  maxOrderID : Option (Terminated 1)  -- tag 9580
  counterPartyOrderCapacity : Option (Terminated 1)  -- tag 9593
  insBidRcvd : Option (Terminated 1)  -- tag 9561
  insAskRcvd : Option (Terminated 1)  -- tag 9562
  insBidSizeRcvd : Option (Terminated 1)  -- tag 9563
  insAskSizeRcvd : Option (Terminated 1)  -- tag 9564
  receiverBid : Option (Terminated 1)  -- tag 9565
  receiverAsk : Option (Terminated 1)  -- tag 9566
  receiverBidSize : Option (Terminated 1)  -- tag 9567
  receiverAskSize : Option (Terminated 1)  -- tag 9568

def NewTrade.parts (record : NewTrade) : List Part :=
  [Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.required [52, 48] record.ordType,
   Part.required [53, 52] record.side,
   Part.required [52, 52] record.price,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 53, 53, 57] record.duration,
   Part.optional [57, 51, 55, 55] record.solicitedFlag,
   Part.optional [57, 53, 50, 56] record.orderCapacity,
   Part.optional [57, 54, 48, 48] record.pingECN,
   Part.optional [57, 55, 49, 48] record.bFMMFlag,
   Part.optional [57, 53, 53, 50] record.counterOrdID,
   Part.required [54, 48] record.transactTime,
   Part.required [57, 54, 54, 53] record.qAPRate,
   Part.required [57, 53, 52, 55] record.liabilityFlag,
   Part.required [57, 53, 53, 49] record.orderQueuePosition,
   Part.optional [57, 53, 52, 57] record.restrictToRoundLots,
   Part.optional [57, 53, 56, 48] record.maxOrderID,
   Part.optional [57, 53, 57, 51] record.counterPartyOrderCapacity,
   Part.optional [57, 53, 54, 49] record.insBidRcvd,
   Part.optional [57, 53, 54, 50] record.insAskRcvd,
   Part.optional [57, 53, 54, 51] record.insBidSizeRcvd,
   Part.optional [57, 53, 54, 52] record.insAskSizeRcvd,
   Part.optional [57, 53, 54, 53] record.receiverBid,
   Part.optional [57, 53, 54, 54] record.receiverAsk,
   Part.optional [57, 53, 54, 55] record.receiverBidSize,
   Part.optional [57, 53, 54, 56] record.receiverAskSize]

def NewTrade.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]], [[52, 48]], [[53, 52]], [[52, 52]], [[51, 56]], [[49, 56]], [[53, 57]], [[57, 53, 53, 57]], [[57, 51, 55, 55]], [[57, 53, 50, 56]], [[57, 54, 48, 48]], [[57, 55, 49, 48]], [[57, 53, 53, 50]], [[54, 48]], [[57, 54, 54, 53]], [[57, 53, 52, 55]], [[57, 53, 53, 49]], [[57, 53, 52, 57]], [[57, 53, 56, 48]], [[57, 53, 57, 51]], [[57, 53, 54, 49]], [[57, 53, 54, 50]], [[57, 53, 54, 51]], [[57, 53, 54, 52]], [[57, 53, 54, 53]], [[57, 53, 54, 54]], [[57, 53, 54, 55]], [[57, 53, 54, 56]]]

theorem NewTrade.shape (record : NewTrade) : record.parts.map Part.tags = NewTrade.tags := rfl

def NewTrade.decode (tokens : List Token) : Option NewTrade := do
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let ordType ← readRequired [52, 48] tokens
  let side ← readRequired [53, 52] tokens
  let price ← readRequired [52, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let duration ← readOptional [57, 53, 53, 57] tokens
  let solicitedFlag ← readOptional [57, 51, 55, 55] tokens
  let orderCapacity ← readOptional [57, 53, 50, 56] tokens
  let pingECN ← readOptional [57, 54, 48, 48] tokens
  let bFMMFlag ← readOptional [57, 55, 49, 48] tokens
  let counterOrdID ← readOptional [57, 53, 53, 50] tokens
  let transactTime ← readRequired [54, 48] tokens
  let qAPRate ← readRequired [57, 54, 54, 53] tokens
  let liabilityFlag ← readRequired [57, 53, 52, 55] tokens
  let orderQueuePosition ← readRequired [57, 53, 53, 49] tokens
  let restrictToRoundLots ← readOptional [57, 53, 52, 57] tokens
  let maxOrderID ← readOptional [57, 53, 56, 48] tokens
  let counterPartyOrderCapacity ← readOptional [57, 53, 57, 51] tokens
  let insBidRcvd ← readOptional [57, 53, 54, 49] tokens
  let insAskRcvd ← readOptional [57, 53, 54, 50] tokens
  let insBidSizeRcvd ← readOptional [57, 53, 54, 51] tokens
  let insAskSizeRcvd ← readOptional [57, 53, 54, 52] tokens
  let receiverBid ← readOptional [57, 53, 54, 53] tokens
  let receiverAsk ← readOptional [57, 53, 54, 54] tokens
  let receiverBidSize ← readOptional [57, 53, 54, 55] tokens
  let receiverAskSize ← readOptional [57, 53, 54, 56] tokens
  pure { symbol, symbolSfx, securityID, iDSource, ordType, side, price, orderQty, execInst, timeInForce, duration, solicitedFlag, orderCapacity, pingECN, bFMMFlag, counterOrdID, transactTime, qAPRate, liabilityFlag, orderQueuePosition, restrictToRoundLots, maxOrderID, counterPartyOrderCapacity, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize }

theorem NewTrade.decode_agrees (record : NewTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ NewTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewTrade.decode tokens = some record := by
  have distinct : NewTrade.tags.flatten.Nodup := by decide +kernel
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have duration := readOptional_part [57, 53, 53, 57] record.duration tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have solicitedFlag := readOptional_part [57, 51, 55, 55] record.solicitedFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderCapacity := readOptional_part [57, 53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have pingECN := readOptional_part [57, 54, 48, 48] record.pingECN tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have bFMMFlag := readOptional_part [57, 55, 49, 48] record.bFMMFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have counterOrdID := readOptional_part [57, 53, 53, 50] record.counterOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have qAPRate := readRequired_part [57, 54, 54, 53] record.qAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have liabilityFlag := readRequired_part [57, 53, 52, 55] record.liabilityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have orderQueuePosition := readRequired_part [57, 53, 53, 49] record.orderQueuePosition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have restrictToRoundLots := readOptional_part [57, 53, 52, 57] record.restrictToRoundLots tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have maxOrderID := readOptional_part [57, 53, 56, 48] record.maxOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have counterPartyOrderCapacity := readOptional_part [57, 53, 57, 51] record.counterPartyOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have insBidRcvd := readOptional_part [57, 53, 54, 49] record.insBidRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have insAskRcvd := readOptional_part [57, 53, 54, 50] record.insAskRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have insBidSizeRcvd := readOptional_part [57, 53, 54, 51] record.insBidSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have insAskSizeRcvd := readOptional_part [57, 53, 54, 52] record.insAskSizeRcvd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have receiverBid := readOptional_part [57, 53, 54, 53] record.receiverBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have receiverAsk := readOptional_part [57, 53, 54, 54] record.receiverAsk tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have receiverBidSize := readOptional_part [57, 53, 54, 55] record.receiverBidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have receiverAskSize := readOptional_part [57, 53, 54, 56] record.receiverAskSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [NewTrade.decode, symbol, symbolSfx, securityID, iDSource, ordType, side, price, orderQty, execInst, timeInForce, duration, solicitedFlag, orderCapacity, pingECN, bFMMFlag, counterOrdID, transactTime, qAPRate, liabilityFlag, orderQueuePosition, restrictToRoundLots, maxOrderID, counterPartyOrderCapacity, insBidRcvd, insAskRcvd, insBidSizeRcvd, insAskSizeRcvd, receiverBid, receiverAsk, receiverBidSize, receiverAskSize, some_bind] <;> rfl

structure CancelTrade where
  maxOrderID : Option (Terminated 1)  -- tag 9580
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22

def CancelTrade.parts (record : CancelTrade) : List Part :=
  [Part.optional [57, 53, 56, 48] record.maxOrderID,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource]

def CancelTrade.tags : List (List (List UInt8)) :=
  [[[57, 53, 56, 48]], [[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]]]

theorem CancelTrade.shape (record : CancelTrade) : record.parts.map Part.tags = CancelTrade.tags := rfl

def CancelTrade.decode (tokens : List Token) : Option CancelTrade := do
  let maxOrderID ← readOptional [57, 53, 56, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  pure { maxOrderID, symbol, symbolSfx, securityID, iDSource }

theorem CancelTrade.decode_agrees (record : CancelTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelTrade.decode tokens = some record := by
  have distinct : CancelTrade.tags.flatten.Nodup := by decide +kernel
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
  simp only [CancelTrade.decode, maxOrderID, symbol, symbolSfx, securityID, iDSource, some_bind] <;> rfl

structure FillDeclineCounterOrReplaceRejected where
  counterOrdID : Option (Terminated 1)  -- tag 9552
  transactTime : Terminated 1  -- tag 60
  resultCode : Terminated 1  -- tag 9548
  text : Terminated 1  -- tag 58

def FillDeclineCounterOrReplaceRejected.parts (record : FillDeclineCounterOrReplaceRejected) : List Part :=
  [Part.optional [57, 53, 53, 50] record.counterOrdID,
   Part.required [54, 48] record.transactTime,
   Part.required [57, 53, 52, 56] record.resultCode,
   Part.required [53, 56] record.text]

def FillDeclineCounterOrReplaceRejected.tags : List (List (List UInt8)) :=
  [[[57, 53, 53, 50]], [[54, 48]], [[57, 53, 52, 56]], [[53, 56]]]

theorem FillDeclineCounterOrReplaceRejected.shape (record : FillDeclineCounterOrReplaceRejected) : record.parts.map Part.tags = FillDeclineCounterOrReplaceRejected.tags := rfl

def FillDeclineCounterOrReplaceRejected.decode (tokens : List Token) : Option FillDeclineCounterOrReplaceRejected := do
  let counterOrdID ← readOptional [57, 53, 53, 50] tokens
  let transactTime ← readRequired [54, 48] tokens
  let resultCode ← readRequired [57, 53, 52, 56] tokens
  let text ← readRequired [53, 56] tokens
  pure { counterOrdID, transactTime, resultCode, text }

theorem FillDeclineCounterOrReplaceRejected.decode_agrees (record : FillDeclineCounterOrReplaceRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ FillDeclineCounterOrReplaceRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    FillDeclineCounterOrReplaceRejected.decode tokens = some record := by
  have distinct : FillDeclineCounterOrReplaceRejected.tags.flatten.Nodup := by decide +kernel
  have counterOrdID := readOptional_part [57, 53, 53, 50] record.counterOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have resultCode := readRequired_part [57, 53, 52, 56] record.resultCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [FillDeclineCounterOrReplaceRejected.decode, counterOrdID, transactTime, resultCode, text, some_bind] <;> rfl

inductive Message where
  | newTrade (header : Header) (r0 : NewTrade)
  | cancelTrade (header : Header) (r0 : CancelTrade)
  | fillDeclineCounterOrReplaceRejected (header : Header) (r0 : FillDeclineCounterOrReplaceRejected)

def Message.tokens : Message → List Token
  | .newTrade header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelTrade header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .fillDeclineCounterOrReplaceRejected header r0 => ⟨[51, 53], ⟨[81], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [68] then
        if known (Header.tags ++ NewTrade.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewTrade.decode rest
          pure (.newTrade header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ CancelTrade.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelTrade.decode rest
          pure (.cancelTrade header r0)
        else none
      else if token.value.val = [81] then
        if known (Header.tags ++ FillDeclineCounterOrReplaceRejected.tags) rest then do
          let header ← Header.decode rest
          let r0 ← FillDeclineCounterOrReplaceRejected.decode rest
          pure (.fillDeclineCounterOrReplaceRejected header r0)
        else none
      else none
    else none

theorem Message.decode_newTrade (header : Header) (r0 : NewTrade) :
    Message.decode (Message.tokens (.newTrade header r0)) = some (.newTrade header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewTrade.tags) rfl rfl (by decide +kernel))
  have c1 := NewTrade.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewTrade.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_cancelTrade (header : Header) (r0 : CancelTrade) :
    Message.decode (Message.tokens (.cancelTrade header r0)) = some (.cancelTrade header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelTrade.tags) rfl rfl (by decide +kernel))
  have c1 := CancelTrade.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelTrade.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_fillDeclineCounterOrReplaceRejected (header : Header) (r0 : FillDeclineCounterOrReplaceRejected) :
    Message.decode (Message.tokens (.fillDeclineCounterOrReplaceRejected header r0)) = some (.fillDeclineCounterOrReplaceRejected header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (FillDeclineCounterOrReplaceRejected.tags) rfl rfl (by decide +kernel))
  have c1 := FillDeclineCounterOrReplaceRejected.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (FillDeclineCounterOrReplaceRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ FillDeclineCounterOrReplaceRejected.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newTrade header r0 => exact Message.decode_newTrade header r0
  | cancelTrade header r0 => exact Message.decode_cancelTrade header r0
  | fillDeclineCounterOrReplaceRejected header r0 => exact Message.decode_fillDeclineCounterOrReplaceRejected header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_newTrade (header : Header) (r0 : NewTrade) :
    Message.decodeBytes (Message.encode (.newTrade header r0)) = some (.newTrade header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newTrade header r0

theorem Message.decodeBytes_cancelTrade (header : Header) (r0 : CancelTrade) :
    Message.decodeBytes (Message.encode (.cancelTrade header r0)) = some (.cancelTrade header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelTrade.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelTrade header r0

theorem Message.decodeBytes_fillDeclineCounterOrReplaceRejected (header : Header) (r0 : FillDeclineCounterOrReplaceRejected) :
    Message.decodeBytes (Message.encode (.fillDeclineCounterOrReplaceRejected header r0)) = some (.fillDeclineCounterOrReplaceRejected header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[81], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ FillDeclineCounterOrReplaceRejected.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_fillDeclineCounterOrReplaceRejected header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newTrade header r0 => exact Message.decodeBytes_newTrade header r0
  | cancelTrade header r0 => exact Message.decodeBytes_cancelTrade header r0
  | fillDeclineCounterOrReplaceRejected header r0 => exact Message.decodeBytes_fillDeclineCounterOrReplaceRejected header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.OtcmarketsLinkatsTrademessagingFixV116Client
