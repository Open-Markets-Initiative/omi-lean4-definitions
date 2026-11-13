import Wire

/-!
# Chicago Board Options Exchange Order Entry v1.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCxaequitiesOrderentryFixV10Client

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

structure NewOrderSingle where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  orderCapacity : Terminated 1  -- tag 47
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Terminated 1  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  undisclosed : Option (Terminated 1)  -- tag 6801
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSellNakedQty : Option (Terminated 1)  -- tag 6803
  shortSellCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSellLongQty : Option (Terminated 1)  -- tag 6805
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

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [52, 55] record.orderCapacity,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [54, 56, 48, 49] record.undisclosed,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSellNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSellCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSellLongQty,
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
   Part.optional [57, 52, 55, 57] record.displayIndicator]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 55]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[54, 56, 48, 49]], [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[55, 54, 57, 57]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[56, 48, 56, 49]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 50]], [[57, 51, 48, 51]], [[57, 52, 55, 57]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let orderCapacity ← readRequired [52, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readRequired [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let undisclosed ← readOptional [54, 56, 48, 49] tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSellNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSellCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSellLongQty ← readOptional [54, 56, 48, 53] tokens
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
  pure { possResend, account, clOrdId, execInst, orderQty, ordType, price, orderCapacity, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, riskGroupID, noTradeFeat, noTradeKey, mEQSE, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderCapacity := readRequired_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have clearingFirm := readRequired_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have undisclosed := readOptional_part [54, 56, 48, 49] record.undisclosed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have shortSellNakedQty := readOptional_part [54, 56, 48, 51] record.shortSellNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have shortSellCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSellCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have shortSellLongQty := readOptional_part [54, 56, 48, 53] record.shortSellLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have riskGroupID := readOptional_part [55, 54, 57, 57] record.riskGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have mEQSE := readOptional_part [56, 48, 56, 49] record.mEQSE tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have brokerPreferencing := readOptional_part [56, 49, 56, 50] record.brokerPreferencing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have displayIndicator := readOptional_part [57, 52, 55, 57] record.displayIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  simp only [NewOrderSingle.decode, possResend, account, clOrdId, execInst, orderQty, ordType, price, orderCapacity, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, riskGroupID, noTradeFeat, noTradeKey, mEQSE, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator, some_bind] <;> rfl

structure OrderCancelRequest where
  possResend : Option (Terminated 1)  -- tag 97
  clOrdId : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [49, 49] record.clOrdId,
   Part.optional [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49, 49]], [[51, 55]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let possResend ← readOptional [57, 55] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  pure { possResend, clOrdId, orderID, origClOrdID, side, symbol, transactTime }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, possResend, clOrdId, orderID, origClOrdID, side, symbol, transactTime, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  possResend : Option (Terminated 1)  -- tag 97
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  orderCapacity : Option (Terminated 1)  -- tag 47
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  undisclosed : Option (Terminated 1)  -- tag 6801
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSellNakedQty : Option (Terminated 1)  -- tag 6803
  shortSellCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSellLongQty : Option (Terminated 1)  -- tag 6805
  noTradeFeat : Option (Terminated 1)  -- tag 7713
  noTradeKey : Option (Terminated 1)  -- tag 7714
  originOfTrans : Option (Terminated 1)  -- tag 8138
  intermediaryID : Option (Terminated 1)  -- tag 8139
  directedWholesaleIndic : Option (Terminated 1)  -- tag 8140
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  brokerPreferencing : Option (Terminated 1)  -- tag 8182
  routingInst : Option (Terminated 1)  -- tag 9303
  displayIndicator : Option (Terminated 1)  -- tag 9479
  cancelOrigOnReject : Option (Terminated 1)  -- tag 9619

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.optional [49, 56] record.execInst,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 55] record.orderCapacity,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [54, 56, 48, 49] record.undisclosed,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSellNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSellCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSellLongQty,
   Part.optional [55, 55, 49, 51] record.noTradeFeat,
   Part.optional [55, 55, 49, 52] record.noTradeKey,
   Part.optional [56, 49, 51, 56] record.originOfTrans,
   Part.optional [56, 49, 51, 57] record.intermediaryID,
   Part.optional [56, 49, 52, 48] record.directedWholesaleIndic,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.optional [56, 49, 56, 50] record.brokerPreferencing,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 52, 55, 57] record.displayIndicator,
   Part.optional [57, 54, 49, 57] record.cancelOrigOnReject]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[49]], [[49, 49]], [[49, 56]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 55]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[54, 56, 48, 49]], [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 50]], [[57, 51, 48, 51]], [[57, 52, 55, 57]], [[57, 54, 49, 57]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let possResend ← readOptional [57, 55] tokens
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let orderCapacity ← readOptional [52, 55] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let undisclosed ← readOptional [54, 56, 48, 49] tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSellNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSellCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSellLongQty ← readOptional [54, 56, 48, 53] tokens
  let noTradeFeat ← readOptional [55, 55, 49, 51] tokens
  let noTradeKey ← readOptional [55, 55, 49, 52] tokens
  let originOfTrans ← readOptional [56, 49, 51, 56] tokens
  let intermediaryID ← readOptional [56, 49, 51, 57] tokens
  let directedWholesaleIndic ← readOptional [56, 49, 52, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let brokerPreferencing ← readOptional [56, 49, 56, 50] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let displayIndicator ← readOptional [57, 52, 55, 57] tokens
  let cancelOrigOnReject ← readOptional [57, 54, 49, 57] tokens
  pure { possResend, account, clOrdId, execInst, orderID, orderQty, ordType, origClOrdID, price, orderCapacity, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, noTradeFeat, noTradeKey, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator, cancelOrigOnReject }

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
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderCapacity := readOptional_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have undisclosed := readOptional_part [54, 56, 48, 49] record.undisclosed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have shortSellNakedQty := readOptional_part [54, 56, 48, 51] record.shortSellNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have shortSellCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSellCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have shortSellLongQty := readOptional_part [54, 56, 48, 53] record.shortSellLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have brokerPreferencing := readOptional_part [56, 49, 56, 50] record.brokerPreferencing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have displayIndicator := readOptional_part [57, 52, 55, 57] record.displayIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have cancelOrigOnReject := readOptional_part [57, 54, 49, 57] record.cancelOrigOnReject tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, possResend, account, clOrdId, execInst, orderID, orderQty, ordType, origClOrdID, price, orderCapacity, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, expireDate, clearingFirm, clearingAccount, undisclosed, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, noTradeFeat, noTradeKey, originOfTrans, intermediaryID, directedWholesaleIndic, removeCrossingFromClearing, brokerPreferencing, routingInst, displayIndicator, cancelOrigOnReject, some_bind] <;> rfl

inductive Message where
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)

def Message.tokens : Message → List Token
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCxaequitiesOrderentryFixV10Client
