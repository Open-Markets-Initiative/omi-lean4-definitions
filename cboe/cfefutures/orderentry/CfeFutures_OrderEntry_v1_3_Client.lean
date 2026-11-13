import Wire

/-!
# Chicago Board Options Exchange Order Entry v1.3, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCfefuturesOrderentryFixV13Client

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

structure NewOrderSingle where
  possResend : Option (Terminated 1)  -- tag 97
  account : Terminated 1  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  maturityMonth : Option (Terminated 1)  -- tag 200
  maturityDay : Option (Terminated 1)  -- tag 205
  securityDesc : Option (Terminated 1)  -- tag 107
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  stopPx : Option (Terminated 1)  -- tag 99
  orderCapacity : Terminated 1  -- tag 47
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126
  minQty : Option (Terminated 1)  -- tag 110
  openClose : Option (Terminated 1)  -- tag 77
  riskReset : Option (Terminated 1)  -- tag 7692
  preventMatch : Option (Terminated 1)  -- tag 7928
  cMTANumber : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  customGroupID : Option (Terminated 1)  -- tag 7699
  cTICode : Terminated 1  -- tag 9702
  manualOrderIndicator : Terminated 1  -- tag 1028
  custOrderHandlingInst : Option (Terminated 1)  -- tag 1031
  oEOID : Terminated 1  -- tag 25004
  frequentTraderID : Option (Terminated 1)  -- tag 21097

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [50, 48, 48] record.maturityMonth,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [57, 57] record.stopPx,
   Part.required [52, 55] record.orderCapacity,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [55, 55] record.openClose,
   Part.optional [55, 54, 57, 50] record.riskReset,
   Part.optional [55, 57, 50, 56] record.preventMatch,
   Part.optional [52, 51, 57] record.cMTANumber,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [55, 54, 57, 57] record.customGroupID,
   Part.required [57, 55, 48, 50] record.cTICode,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.optional [49, 48, 51, 49] record.custOrderHandlingInst,
   Part.required [50, 53, 48, 48, 52] record.oEOID,
   Part.optional [50, 49, 48, 57, 55] record.frequentTraderID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[54, 48]], [[49, 54, 55]], [[53, 53]], [[50, 48, 48]], [[50, 48, 53]], [[49, 48, 55]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[57, 57]], [[52, 55]], [[53, 57]], [[49, 50, 54]], [[49, 49, 48]], [[55, 55]], [[55, 54, 57, 50]], [[55, 57, 50, 56]], [[52, 51, 57]], [[52, 52, 48]], [[55, 54, 57, 57]], [[57, 55, 48, 50]], [[49, 48, 50, 56]], [[49, 48, 51, 49]], [[50, 53, 48, 48, 52]], [[50, 49, 48, 57, 55]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readRequired [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let maturityMonth ← readOptional [50, 48, 48] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let stopPx ← readOptional [57, 57] tokens
  let orderCapacity ← readRequired [52, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let openClose ← readOptional [55, 55] tokens
  let riskReset ← readOptional [55, 54, 57, 50] tokens
  let preventMatch ← readOptional [55, 57, 50, 56] tokens
  let cMTANumber ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let customGroupID ← readOptional [55, 54, 57, 57] tokens
  let cTICode ← readRequired [57, 55, 48, 50] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let custOrderHandlingInst ← readOptional [49, 48, 51, 49] tokens
  let oEOID ← readRequired [50, 53, 48, 48, 52] tokens
  let frequentTraderID ← readOptional [50, 49, 48, 57, 55] tokens
  pure { possResend, account, clOrdId, transactTime, securityType, symbol, maturityMonth, maturityDay, securityDesc, side, orderQty, ordType, price, stopPx, orderCapacity, timeInForce, expireTime, minQty, openClose, riskReset, preventMatch, cMTANumber, clearingAccount, customGroupID, cTICode, manualOrderIndicator, custOrderHandlingInst, oEOID, frequentTraderID }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityMonth := readOptional_part [50, 48, 48] record.maturityMonth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderCapacity := readRequired_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have riskReset := readOptional_part [55, 54, 57, 50] record.riskReset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have preventMatch := readOptional_part [55, 57, 50, 56] record.preventMatch tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have cMTANumber := readOptional_part [52, 51, 57] record.cMTANumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customGroupID := readOptional_part [55, 54, 57, 57] record.customGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have cTICode := readRequired_part [57, 55, 48, 50] record.cTICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have custOrderHandlingInst := readOptional_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have oEOID := readRequired_part [50, 53, 48, 48, 52] record.oEOID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have frequentTraderID := readOptional_part [50, 49, 48, 57, 55] record.frequentTraderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  simp only [NewOrderSingle.decode, possResend, account, clOrdId, transactTime, securityType, symbol, maturityMonth, maturityDay, securityDesc, side, orderQty, ordType, price, stopPx, orderCapacity, timeInForce, expireTime, minQty, openClose, riskReset, preventMatch, cMTANumber, clearingAccount, customGroupID, cTICode, manualOrderIndicator, custOrderHandlingInst, oEOID, frequentTraderID, some_bind] <;> rfl

structure OrderCancelRequest where
  possResend : Option (Terminated 1)  -- tag 97
  clOrdId : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderId : Option (Terminated 1)  -- tag 37
  transactTime : Terminated 1  -- tag 60
  symbol : Option (Terminated 1)  -- tag 55
  massCancelInst : Option (Terminated 1)  -- tag 7700
  massCancelID : Option (Terminated 1)  -- tag 7695
  manualOrderIndicator : Terminated 1  -- tag 1028
  oEOID : Terminated 1  -- tag 25004

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [49, 49] record.clOrdId,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderId,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 55, 48, 48] record.massCancelInst,
   Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.required [50, 53, 48, 48, 52] record.oEOID]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49, 49]], [[52, 49]], [[51, 55]], [[54, 48]], [[53, 53]], [[55, 55, 48, 48]], [[55, 54, 57, 53]], [[49, 48, 50, 56]], [[50, 53, 48, 48, 52]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let possResend ← readOptional [57, 55] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let massCancelInst ← readOptional [55, 55, 48, 48] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let oEOID ← readRequired [50, 53, 48, 48, 52] tokens
  pure { possResend, clOrdId, origClOrdID, orderId, transactTime, symbol, massCancelInst, massCancelID, manualOrderIndicator, oEOID }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have massCancelInst := readOptional_part [55, 55, 48, 48] record.massCancelInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have oEOID := readRequired_part [50, 53, 48, 48, 52] record.oEOID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, possResend, clOrdId, origClOrdID, orderId, transactTime, symbol, massCancelInst, massCancelID, manualOrderIndicator, oEOID, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  origClOrdID : Option (Terminated 1)  -- tag 41
  orderId : Option (Terminated 1)  -- tag 37
  transactTime : Terminated 1  -- tag 60
  side : Option (Terminated 1)  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  price : Terminated 1  -- tag 44
  stopPx : Option (Terminated 1)  -- tag 99
  cancelOrigOnReject : Option (Terminated 1)  -- tag 9619
  manualOrderIndicator : Terminated 1  -- tag 1028
  custOrderHandlingInst : Option (Terminated 1)  -- tag 1031
  oEOID : Terminated 1  -- tag 25004
  frequentTraderID : Option (Terminated 1)  -- tag 21097

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderId,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.optional [57, 57] record.stopPx,
   Part.optional [57, 54, 49, 57] record.cancelOrigOnReject,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.optional [49, 48, 51, 49] record.custOrderHandlingInst,
   Part.required [50, 53, 48, 48, 52] record.oEOID,
   Part.optional [50, 49, 48, 57, 55] record.frequentTraderID]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[52, 49]], [[51, 55]], [[54, 48]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[57, 57]], [[57, 54, 49, 57]], [[49, 48, 50, 56]], [[49, 48, 51, 49]], [[50, 53, 48, 48, 52]], [[50, 49, 48, 57, 55]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let stopPx ← readOptional [57, 57] tokens
  let cancelOrigOnReject ← readOptional [57, 54, 49, 57] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let custOrderHandlingInst ← readOptional [49, 48, 51, 49] tokens
  let oEOID ← readRequired [50, 53, 48, 48, 52] tokens
  let frequentTraderID ← readOptional [50, 49, 48, 57, 55] tokens
  pure { possResend, account, clOrdId, origClOrdID, orderId, transactTime, side, orderQty, ordType, price, stopPx, cancelOrigOnReject, manualOrderIndicator, custOrderHandlingInst, oEOID, frequentTraderID }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have cancelOrigOnReject := readOptional_part [57, 54, 49, 57] record.cancelOrigOnReject tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have custOrderHandlingInst := readOptional_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have oEOID := readRequired_part [50, 53, 48, 48, 52] record.oEOID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have frequentTraderID := readOptional_part [50, 49, 48, 57, 55] record.frequentTraderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, possResend, account, clOrdId, origClOrdID, orderId, transactTime, side, orderQty, ordType, price, stopPx, cancelOrigOnReject, manualOrderIndicator, custOrderHandlingInst, oEOID, frequentTraderID, some_bind] <;> rfl

structure SecurityDefinitionRequestOptionsOnly where
  possResend : Option (Terminated 1)  -- tag 97
  clOrdId : Option (Terminated 1)  -- tag 11
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Option (Terminated 1)  -- tag 167

def SecurityDefinitionRequestOptionsOnly.parts (record : SecurityDefinitionRequestOptionsOnly) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49, 49] record.clOrdId,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 54, 55] record.securityType]

def SecurityDefinitionRequestOptionsOnly.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49, 49]], [[54, 48]], [[49, 54, 55]]]

theorem SecurityDefinitionRequestOptionsOnly.shape (record : SecurityDefinitionRequestOptionsOnly) : record.parts.map Part.tags = SecurityDefinitionRequestOptionsOnly.tags := rfl

def SecurityDefinitionRequestOptionsOnly.decode (tokens : List Token) : Option SecurityDefinitionRequestOptionsOnly := do
  let possResend ← readOptional [57, 55] tokens
  let clOrdId ← readOptional [49, 49] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  pure { possResend, clOrdId, transactTime, securityType }

theorem SecurityDefinitionRequestOptionsOnly.decode_agrees (record : SecurityDefinitionRequestOptionsOnly) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequestOptionsOnly.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequestOptionsOnly.decode tokens = some record := by
  have distinct : SecurityDefinitionRequestOptionsOnly.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readOptional_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityDefinitionRequestOptionsOnly.decode, possResend, clOrdId, transactTime, securityType, some_bind] <;> rfl

inductive Message where
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | securityDefinitionRequestOptionsOnly (header : Header) (r0 : SecurityDefinitionRequestOptionsOnly)

def Message.tokens : Message → List Token
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequestOptionsOnly header r0 => ⟨[51, 53], ⟨[99], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [99] then
        if known (Header.tags ++ SecurityDefinitionRequestOptionsOnly.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequestOptionsOnly.decode rest
          pure (.securityDefinitionRequestOptionsOnly header r0)
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

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequestOptionsOnly (header : Header) (r0 : SecurityDefinitionRequestOptionsOnly) :
    Message.decode (Message.tokens (.securityDefinitionRequestOptionsOnly header r0)) = some (.securityDefinitionRequestOptionsOnly header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequestOptionsOnly.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequestOptionsOnly.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequestOptionsOnly.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequestOptionsOnly.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | securityDefinitionRequestOptionsOnly header r0 => exact Message.decode_securityDefinitionRequestOptionsOnly header r0

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

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_securityDefinitionRequestOptionsOnly (header : Header) (r0 : SecurityDefinitionRequestOptionsOnly) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequestOptionsOnly header r0)) = some (.securityDefinitionRequestOptionsOnly header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[99], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequestOptionsOnly.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequestOptionsOnly header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | securityDefinitionRequestOptionsOnly header r0 => exact Message.decodeBytes_securityDefinitionRequestOptionsOnly header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCfefuturesOrderentryFixV13Client
