import Wire

/-!
# Chicago Board Options Exchange Order Entry v8.73, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBidsjapanOrderentryFixV873Client

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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Option (Terminated 1)  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  iOIid : Option (Terminated 1)  -- tag 23
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  rule80A : Option (Terminated 1)  -- tag 47
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  settlmntTyp : Option (Terminated 1)  -- tag 63
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  exDestination : Option (Terminated 1)  -- tag 100
  minQty : Option (Terminated 1)  -- tag 110
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
  securityExchange : Option (Terminated 1)  -- tag 207
  pegDifference : Option (Terminated 1)  -- tag 211
  complianceID : Option (Terminated 1)  -- tag 376
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  clearingFirm : Option (Terminated 1)  -- tag 439
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  orderCapacity : Option (Terminated 1)  -- tag 528
  bookingType : Option (Terminated 1)  -- tag 775
  shortSaleExemptionReason : Option (Terminated 1)  -- tag 1688
  locateBroker : Option (Terminated 1)  -- tag 5700
  locateIdentifier : Option (Terminated 1)  -- tag 5701
  partyIDOrderOriginationFirm : Option (Terminated 1)  -- tag 20013

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.optional [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.optional [50, 51] record.iOIid,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.rule80A,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 55, 54] record.complianceID,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 55, 53] record.bookingType,
   Part.optional [49, 54, 56, 56] record.shortSaleExemptionReason,
   Part.optional [53, 55, 48, 48] record.locateBroker,
   Part.optional [53, 55, 48, 49] record.locateIdentifier,
   Part.optional [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[50, 51]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 55]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 51]], [[54, 53]], [[55, 54]], [[49, 48, 48]], [[49, 49, 48]], [[49, 49, 52]], [[49, 50, 54]], [[50, 48, 55]], [[50, 49, 49]], [[51, 55, 54]], [[51, 56, 56]], [[51, 56, 57]], [[52, 51, 57]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[53, 50, 56]], [[55, 55, 53]], [[49, 54, 56, 56]], [[53, 55, 48, 48]], [[53, 55, 48, 49]], [[50, 48, 48, 49, 51]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readOptional [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let iOIid ← readOptional [50, 51] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let rule80A ← readOptional [52, 55] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let complianceID ← readOptional [51, 55, 54] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  let shortSaleExemptionReason ← readOptional [49, 54, 56, 56] tokens
  let locateBroker ← readOptional [53, 55, 48, 48] tokens
  let locateIdentifier ← readOptional [53, 55, 48, 49] tokens
  let partyIDOrderOriginationFirm ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, currency, execInst, handlInst, iDSource, iOIid, orderQty, ordType, price, rule80A, securityID, side, symbol, text, timeInForce, transactTime, settlmntTyp, symbolSfx, execBroker, exDestination, minQty, locateReqd, expireTime, securityExchange, pegDifference, complianceID, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, bookingType, shortSaleExemptionReason, locateBroker, locateIdentifier, partyIDOrderOriginationFirm }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have iOIid := readOptional_part [50, 51] record.iOIid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have complianceID := readOptional_part [51, 55, 54] record.complianceID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have shortSaleExemptionReason := readOptional_part [49, 54, 56, 56] record.shortSaleExemptionReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have locateIdentifier := readOptional_part [53, 55, 48, 49] record.locateIdentifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have partyIDOrderOriginationFirm := readOptional_part [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, currency, execInst, handlInst, iDSource, iOIid, orderQty, ordType, price, rule80A, securityID, side, symbol, text, timeInForce, transactTime, settlmntTyp, symbolSfx, execBroker, exDestination, minQty, locateReqd, expireTime, securityExchange, pegDifference, complianceID, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, bookingType, shortSaleExemptionReason, locateBroker, locateIdentifier, partyIDOrderOriginationFirm, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Option (Terminated 1)  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  rule80A : Option (Terminated 1)  -- tag 47
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  settlmntTyp : Option (Terminated 1)  -- tag 63
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  exDestination : Option (Terminated 1)  -- tag 100
  minQty : Option (Terminated 1)  -- tag 110
  locateReqd : Option (Terminated 1)  -- tag 114
  expireTime : Option (Terminated 1)  -- tag 126
  securityExchange : Option (Terminated 1)  -- tag 207
  pegDifference : Option (Terminated 1)  -- tag 211
  complianceID : Option (Terminated 1)  -- tag 376
  discretionInst : Option (Terminated 1)  -- tag 388
  discretionOffset : Option (Terminated 1)  -- tag 389
  clearingFirm : Option (Terminated 1)  -- tag 439
  partyID : Option (Terminated 1)  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  orderCapacity : Option (Terminated 1)  -- tag 528
  bookingType : Option (Terminated 1)  -- tag 775
  shortSaleExemptionReason : Option (Terminated 1)  -- tag 1688
  locateBroker : Option (Terminated 1)  -- tag 5700
  locateIdentifier : Option (Terminated 1)  -- tag 5701
  partyIDOrderOriginationFirm : Option (Terminated 1)  -- tag 20013

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.optional [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.rule80A,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [51, 55, 54] record.complianceID,
   Part.optional [51, 56, 56] record.discretionInst,
   Part.optional [51, 56, 57] record.discretionOffset,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 55, 53] record.bookingType,
   Part.optional [49, 54, 56, 56] record.shortSaleExemptionReason,
   Part.optional [53, 55, 48, 48] record.locateBroker,
   Part.optional [53, 55, 48, 49] record.locateIdentifier,
   Part.optional [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 55]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[54, 51]], [[54, 53]], [[55, 54]], [[49, 48, 48]], [[49, 49, 48]], [[49, 49, 52]], [[49, 50, 54]], [[50, 48, 55]], [[50, 49, 49]], [[51, 55, 54]], [[51, 56, 56]], [[51, 56, 57]], [[52, 51, 57]], [[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[53, 50, 56]], [[55, 55, 53]], [[49, 54, 56, 56]], [[53, 55, 48, 48]], [[53, 55, 48, 49]], [[50, 48, 48, 49, 51]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readOptional [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let rule80A ← readOptional [52, 55] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let complianceID ← readOptional [51, 55, 54] tokens
  let discretionInst ← readOptional [51, 56, 56] tokens
  let discretionOffset ← readOptional [51, 56, 57] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  let shortSaleExemptionReason ← readOptional [49, 54, 56, 56] tokens
  let locateBroker ← readOptional [53, 55, 48, 48] tokens
  let locateIdentifier ← readOptional [53, 55, 48, 49] tokens
  let partyIDOrderOriginationFirm ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, currency, execInst, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, rule80A, securityID, side, symbol, text, timeInForce, transactTime, settlmntTyp, symbolSfx, execBroker, exDestination, minQty, locateReqd, expireTime, securityExchange, pegDifference, complianceID, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, bookingType, shortSaleExemptionReason, locateBroker, locateIdentifier, partyIDOrderOriginationFirm }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have complianceID := readOptional_part [51, 55, 54] record.complianceID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have discretionInst := readOptional_part [51, 56, 56] record.discretionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have discretionOffset := readOptional_part [51, 56, 57] record.discretionOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have shortSaleExemptionReason := readOptional_part [49, 54, 56, 56] record.shortSaleExemptionReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have locateBroker := readOptional_part [53, 55, 48, 48] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have locateIdentifier := readOptional_part [53, 55, 48, 49] record.locateIdentifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have partyIDOrderOriginationFirm := readOptional_part [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, currency, execInst, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, rule80A, securityID, side, symbol, text, timeInForce, transactTime, settlmntTyp, symbolSfx, execBroker, exDestination, minQty, locateReqd, expireTime, securityExchange, pegDifference, complianceID, discretionInst, discretionOffset, clearingFirm, partyID, partyIDSource, partyRole, orderCapacity, bookingType, shortSaleExemptionReason, locateBroker, locateIdentifier, partyIDOrderOriginationFirm, some_bind] <;> rfl

structure OrderCancelRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Option (Terminated 1)  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Option (Terminated 1)  -- tag 65
  execBroker : Option (Terminated 1)  -- tag 76
  securityExchange : Option (Terminated 1)  -- tag 207
  complianceID : Option (Terminated 1)  -- tag 376
  clearingFirm : Option (Terminated 1)  -- tag 439
  bookingType : Option (Terminated 1)  -- tag 775

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [55, 54] record.execBroker,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [51, 55, 54] record.complianceID,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 55, 53] record.bookingType]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[50, 50]], [[51, 55]], [[51, 56]], [[52, 49]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[54, 48]], [[54, 53]], [[55, 54]], [[50, 48, 55]], [[51, 55, 54]], [[52, 51, 57]], [[55, 55, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readOptional [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let complianceID ← readOptional [51, 55, 54] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  pure { account, clOrdID, currency, iDSource, orderID, orderQty, origClOrdID, securityID, side, symbol, text, transactTime, symbolSfx, execBroker, securityExchange, complianceID, clearingFirm, bookingType }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have complianceID := readOptional_part [51, 55, 54] record.complianceID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, account, clOrdID, currency, iDSource, orderID, orderQty, origClOrdID, securityID, side, symbol, text, transactTime, symbolSfx, execBroker, securityExchange, complianceID, clearingFirm, bookingType, some_bind] <;> rfl

inductive Message where
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)

def Message.tokens : Message → List Token
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
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
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

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
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeBidsjapanOrderentryFixV873Client
