import Wire

/-!
# New York Stock Exchange NYSE Pillar Gateway Floor Broker v2.6, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NyseNyseequitiesFloorbrokerFixV26Client

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

structure NewOrder where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
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
  introducingBadgeID : Terminated 1  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  parentFirmClOrdID : Terminated 1  -- tag 9451
  interestType : Option (Terminated 1)  -- tag 9478
  dOrderAuctionPrice : Option (Terminated 1)  -- tag 9565
  attributedQuote : Option (Terminated 1)  -- tag 20001
  proactiveIfLocked : Option (Terminated 1)  -- tag 20002
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013
  cATIMID : Option (Terminated 1)  -- tag 20042
  targetStrategy : Option (Terminated 1)  -- tag 20046
  f10b18 : Option (Terminated 1)  -- tag 20047
  auctionEligible : Option (Terminated 1)  -- tag 20048
  minParticpationRate : Option (Terminated 1)  -- tag 20049
  maxParticipationRate : Option (Terminated 1)  -- tag 20050
  wouldPrice : Option (Terminated 1)  -- tag 20051

def NewOrder.parts (record : NewOrder) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
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
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.required [57, 52, 53, 49] record.parentFirmClOrdID,
   Part.optional [57, 52, 55, 56] record.interestType,
   Part.optional [57, 53, 54, 53] record.dOrderAuctionPrice,
   Part.optional [50, 48, 48, 48, 49] record.attributedQuote,
   Part.optional [50, 48, 48, 48, 50] record.proactiveIfLocked,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator,
   Part.optional [50, 48, 48, 52, 50] record.cATIMID,
   Part.optional [50, 48, 48, 52, 54] record.targetStrategy,
   Part.optional [50, 48, 48, 52, 55] record.f10b18,
   Part.optional [50, 48, 48, 52, 56] record.auctionEligible,
   Part.optional [50, 48, 48, 52, 57] record.minParticpationRate,
   Part.optional [50, 48, 48, 53, 48] record.maxParticipationRate,
   Part.optional [50, 48, 48, 53, 49] record.wouldPrice]

def NewOrder.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 53]], [[49, 49, 48]], [[49, 49, 49]], [[49, 49, 52]], [[49, 50, 54]], [[49, 54, 56]], [[51, 56, 54]], [[51, 51, 54]], [[53, 50, 56]], [[56, 52, 57]], [[53, 55, 48, 48]], [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 51, 48, 51]], [[57, 52, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[57, 52, 53, 49]], [[57, 52, 55, 56]], [[57, 53, 54, 53]], [[50, 48, 48, 48, 49]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 52, 50]], [[50, 48, 48, 52, 54]], [[50, 48, 48, 52, 55]], [[50, 48, 48, 52, 56]], [[50, 48, 48, 52, 57]], [[50, 48, 48, 53, 48]], [[50, 48, 48, 53, 49]]]

theorem NewOrder.shape (record : NewOrder) : record.parts.map Part.tags = NewOrder.tags := rfl

def NewOrder.decode (tokens : List Token) : Option NewOrder := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
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
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let parentFirmClOrdID ← readRequired [57, 52, 53, 49] tokens
  let interestType ← readOptional [57, 52, 55, 56] tokens
  let dOrderAuctionPrice ← readOptional [57, 53, 54, 53] tokens
  let attributedQuote ← readOptional [50, 48, 48, 48, 49] tokens
  let proactiveIfLocked ← readOptional [50, 48, 48, 48, 50] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  let cATIMID ← readOptional [50, 48, 48, 52, 50] tokens
  let targetStrategy ← readOptional [50, 48, 48, 52, 54] tokens
  let f10b18 ← readOptional [50, 48, 48, 52, 55] tokens
  let auctionEligible ← readOptional [50, 48, 48, 52, 56] tokens
  let minParticpationRate ← readOptional [50, 48, 48, 52, 57] tokens
  let maxParticipationRate ← readOptional [50, 48, 48, 53, 48] tokens
  let wouldPrice ← readOptional [50, 48, 48, 53, 49] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, symbolSfx, minQty, maxFloor, locateReqd, expireTime, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dOrderAuctionPrice, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice }

theorem NewOrder.decode_agrees (record : NewOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrder.decode tokens = some record := by
  have distinct : NewOrder.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noTradingSessions := readRequired_part [51, 56, 54] record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have participationRate := readOptional_part [56, 52, 57] record.participationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have offsetPrice := readOptional_part [57, 52, 48, 51] record.offsetPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have parentFirmClOrdID := readRequired_part [57, 52, 53, 49] record.parentFirmClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have interestType := readOptional_part [57, 52, 55, 56] record.interestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have dOrderAuctionPrice := readOptional_part [57, 53, 54, 53] record.dOrderAuctionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have attributedQuote := readOptional_part [50, 48, 48, 48, 49] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have proactiveIfLocked := readOptional_part [50, 48, 48, 48, 50] record.proactiveIfLocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have cATIMID := readOptional_part [50, 48, 48, 52, 50] record.cATIMID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have targetStrategy := readOptional_part [50, 48, 48, 52, 54] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have f10b18 := readOptional_part [50, 48, 48, 52, 55] record.f10b18 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have auctionEligible := readOptional_part [50, 48, 48, 52, 56] record.auctionEligible tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have minParticpationRate := readOptional_part [50, 48, 48, 52, 57] record.minParticpationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have maxParticipationRate := readOptional_part [50, 48, 48, 53, 48] record.maxParticipationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have wouldPrice := readOptional_part [50, 48, 48, 53, 49] record.wouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  simp only [NewOrder.decode, account, clOrdID, execInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, symbolSfx, minQty, maxFloor, locateReqd, expireTime, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dOrderAuctionPrice, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
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
  introducingBadgeID : Terminated 1  -- tag 9448
  billTo : Option (Terminated 1)  -- tag 9449
  parentFirmClOrdID : Terminated 1  -- tag 9451
  interestType : Option (Terminated 1)  -- tag 9478
  dOrderAuctionPrice : Option (Terminated 1)  -- tag 9565
  attributedQuote : Option (Terminated 1)  -- tag 20001
  proactiveIfLocked : Option (Terminated 1)  -- tag 20002
  cancelInsteadOfReprice : Option (Terminated 1)  -- tag 20003
  subIDIndicator : Option (Terminated 1)  -- tag 20013
  cATIMID : Option (Terminated 1)  -- tag 20042
  targetStrategy : Option (Terminated 1)  -- tag 20046
  f10b18 : Option (Terminated 1)  -- tag 20047
  auctionEligible : Option (Terminated 1)  -- tag 20048
  minParticpationRate : Option (Terminated 1)  -- tag 20049
  maxParticipationRate : Option (Terminated 1)  -- tag 20050
  wouldPrice : Option (Terminated 1)  -- tag 20051

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
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
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 52, 57] record.billTo,
   Part.required [57, 52, 53, 49] record.parentFirmClOrdID,
   Part.optional [57, 52, 55, 56] record.interestType,
   Part.optional [57, 53, 54, 53] record.dOrderAuctionPrice,
   Part.optional [50, 48, 48, 48, 49] record.attributedQuote,
   Part.optional [50, 48, 48, 48, 50] record.proactiveIfLocked,
   Part.optional [50, 48, 48, 48, 51] record.cancelInsteadOfReprice,
   Part.optional [50, 48, 48, 49, 51] record.subIDIndicator,
   Part.optional [50, 48, 48, 52, 50] record.cATIMID,
   Part.optional [50, 48, 48, 52, 54] record.targetStrategy,
   Part.optional [50, 48, 48, 52, 55] record.f10b18,
   Part.optional [50, 48, 48, 52, 56] record.auctionEligible,
   Part.optional [50, 48, 48, 52, 57] record.minParticpationRate,
   Part.optional [50, 48, 48, 53, 48] record.maxParticipationRate,
   Part.optional [50, 48, 48, 53, 49] record.wouldPrice]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 53]], [[49, 49, 48]], [[49, 49, 49]], [[49, 49, 52]], [[49, 50, 54]], [[49, 54, 56]], [[51, 56, 54]], [[51, 51, 54]], [[53, 50, 56]], [[56, 52, 57]], [[53, 55, 48, 48]], [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 51, 48, 51]], [[57, 52, 48, 51]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 52, 57]], [[57, 52, 53, 49]], [[57, 52, 55, 56]], [[57, 53, 54, 53]], [[50, 48, 48, 48, 49]], [[50, 48, 48, 48, 50]], [[50, 48, 48, 48, 51]], [[50, 48, 48, 49, 51]], [[50, 48, 48, 52, 50]], [[50, 48, 48, 52, 54]], [[50, 48, 48, 52, 55]], [[50, 48, 48, 52, 56]], [[50, 48, 48, 52, 57]], [[50, 48, 48, 53, 48]], [[50, 48, 48, 53, 49]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
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
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let billTo ← readOptional [57, 52, 52, 57] tokens
  let parentFirmClOrdID ← readRequired [57, 52, 53, 49] tokens
  let interestType ← readOptional [57, 52, 55, 56] tokens
  let dOrderAuctionPrice ← readOptional [57, 53, 54, 53] tokens
  let attributedQuote ← readOptional [50, 48, 48, 48, 49] tokens
  let proactiveIfLocked ← readOptional [50, 48, 48, 48, 50] tokens
  let cancelInsteadOfReprice ← readOptional [50, 48, 48, 48, 51] tokens
  let subIDIndicator ← readOptional [50, 48, 48, 49, 51] tokens
  let cATIMID ← readOptional [50, 48, 48, 52, 50] tokens
  let targetStrategy ← readOptional [50, 48, 48, 52, 54] tokens
  let f10b18 ← readOptional [50, 48, 48, 52, 55] tokens
  let auctionEligible ← readOptional [50, 48, 48, 52, 56] tokens
  let minParticpationRate ← readOptional [50, 48, 48, 52, 57] tokens
  let maxParticipationRate ← readOptional [50, 48, 48, 53, 48] tokens
  let wouldPrice ← readOptional [50, 48, 48, 53, 49] tokens
  pure { account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, symbolSfx, minQty, maxFloor, locateReqd, expireTime, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dOrderAuctionPrice, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noTradingSessions := readRequired_part [51, 56, 54] record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have participationRate := readOptional_part [56, 52, 57] record.participationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have offsetPrice := readOptional_part [57, 52, 48, 51] record.offsetPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have billTo := readOptional_part [57, 52, 52, 57] record.billTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have parentFirmClOrdID := readRequired_part [57, 52, 53, 49] record.parentFirmClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have interestType := readOptional_part [57, 52, 55, 56] record.interestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have dOrderAuctionPrice := readOptional_part [57, 53, 54, 53] record.dOrderAuctionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have attributedQuote := readOptional_part [50, 48, 48, 48, 49] record.attributedQuote tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have proactiveIfLocked := readOptional_part [50, 48, 48, 48, 50] record.proactiveIfLocked tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have cancelInsteadOfReprice := readOptional_part [50, 48, 48, 48, 51] record.cancelInsteadOfReprice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have subIDIndicator := readOptional_part [50, 48, 48, 49, 51] record.subIDIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have cATIMID := readOptional_part [50, 48, 48, 52, 50] record.cATIMID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have targetStrategy := readOptional_part [50, 48, 48, 52, 54] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have f10b18 := readOptional_part [50, 48, 48, 52, 55] record.f10b18 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have auctionEligible := readOptional_part [50, 48, 48, 52, 56] record.auctionEligible tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have minParticpationRate := readOptional_part [50, 48, 48, 52, 57] record.minParticpationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have maxParticipationRate := readOptional_part [50, 48, 48, 53, 48] record.maxParticipationRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have wouldPrice := readOptional_part [50, 48, 48, 53, 49] record.wouldPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, execInst, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, symbolSfx, minQty, maxFloor, locateReqd, expireTime, effectiveTime, noTradingSessions, tradingSessionID, orderCapacity, participationRate, locateBroker, selfTradeType, specialOrdType, routingInst, offsetPrice, extendedExecInst, introducingBadgeID, billTo, parentFirmClOrdID, interestType, dOrderAuctionPrice, attributedQuote, proactiveIfLocked, cancelInsteadOfReprice, subIDIndicator, cATIMID, targetStrategy, f10b18, auctionEligible, minParticpationRate, maxParticipationRate, wouldPrice, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  pure { clOrdID, orderID, origClOrdID, side, symbol, transactTime, symbolSfx }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, orderID, origClOrdID, side, symbol, transactTime, symbolSfx, some_bind] <;> rfl

inductive Message where
  | newOrder (header : Header) (r0 : NewOrder)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)

def Message.tokens : Message → List Token
  | .newOrder header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [68] then
        if known (Header.tags ++ NewOrder.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrder.decode rest
          pure (.newOrder header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else none
    else none

theorem Message.decode_newOrder (header : Header) (r0 : NewOrder) :
    Message.decode (Message.tokens (.newOrder header r0)) = some (.newOrder header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrder.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrder.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrder.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newOrder header r0 => exact Message.decode_newOrder header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_newOrder (header : Header) (r0 : NewOrder) :
    Message.decodeBytes (Message.encode (.newOrder header r0)) = some (.newOrder header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrder.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrder header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newOrder header r0 => exact Message.decodeBytes_newOrder header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NyseNyseequitiesFloorbrokerFixV26Client
