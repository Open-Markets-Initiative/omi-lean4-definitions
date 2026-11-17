import Wire

/-!
# Coinbase Order Entry v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CoinbaseDeribitOrderentryFixV10Exchange

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Option (Terminated 1)  -- tag 52

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [53, 50] record.sendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readOptional [53, 50] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_none pairing))))

structure NoFills where
  fillExecID : Terminated 1  -- tag 1363
  fillPx : Option (Terminated 1)  -- tag 1364
  fillQty : Option (Terminated 1)  -- tag 1365
  fillLiquidityInd : Option (Terminated 1)  -- tag 1443

def NoFills.parts (record : NoFills) : List Part :=
  [Part.required [49, 51, 54, 51] record.fillExecID,
   Part.optional [49, 51, 54, 52] record.fillPx,
   Part.optional [49, 51, 54, 53] record.fillQty,
   Part.optional [49, 52, 52, 51] record.fillLiquidityInd]

def NoFills.tags : List (List (List UInt8)) :=
  [[[49, 51, 54, 51]], [[49, 51, 54, 52]], [[49, 51, 54, 53]], [[49, 52, 52, 51]]]

theorem NoFills.shape (record : NoFills) : record.parts.map Part.tags = NoFills.tags := rfl

def NoFills.decode (tokens : List Token) : Option NoFills := do
  let fillExecID ← readRequired [49, 51, 54, 51] tokens
  let fillPx ← readOptional [49, 51, 54, 52] tokens
  let fillQty ← readOptional [49, 51, 54, 53] tokens
  let fillLiquidityInd ← readOptional [49, 52, 52, 51] tokens
  pure { fillExecID, fillPx, fillQty, fillLiquidityInd }

theorem NoFills.decode_agrees (record : NoFills) (tokens : List Token)
    (agrees : ∀ tags ∈ NoFills.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoFills.decode tokens = some record := by
  have distinct : NoFills.tags.flatten.Nodup := by decide +kernel
  have fillExecID := readRequired_part [49, 51, 54, 51] record.fillExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have fillPx := readOptional_part [49, 51, 54, 52] record.fillPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have fillQty := readOptional_part [49, 51, 54, 53] record.fillQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have fillLiquidityInd := readOptional_part [49, 52, 52, 51] record.fillLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoFills.decode, fillExecID, fillPx, fillQty, fillLiquidityInd, some_bind] <;> rfl

theorem NoFills.taken (record : NoFills) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 51] record.fillExecID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 51, 54, 52] record.fillPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 51, 54, 53] record.fillQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 52, 51] record.fillLiquidityInd (by decide) (by decide))
      (paired_none pairing))))

def NoFills.members : List (List UInt8) := NoFills.tags.flatten

def NoFills.encode (entry : NoFills) : List Token := encodeParts entry.parts

theorem NoFills.decode_encode (entry : NoFills) : NoFills.decode entry.encode = some entry :=
  NoFills.decode_agrees entry _ (fun _ _ => rfl)

theorem NoFills.within (entry : NoFills) : ∀ token ∈ entry.encode, token.tag ∈ NoFills.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoFills.shape] at this

theorem NoFills.led (entry : NoFills) : Lead [49, 51, 54, 51] entry.encode :=
  lead_parts [49, 51, 54, 51] entry.fillExecID _ NoFills.tags.tail rfl (by decide +kernel)

structure ExecutionReport where
  secondaryExecID : Option (Terminated 1)  -- tag 527
  orderId : Option (Terminated 1)  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdId : Option (Terminated 1)  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  commission : Option (Terminated 1)  -- tag 12
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  orderQty : Terminated 1  -- tag 38
  cashOrderQty : Option (Terminated 1)  -- tag 152
  conditionTriggerMethod : Option (Terminated 1)  -- tag 5127
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  execType : Option (Terminated 1)  -- tag 150
  execInst : Option (Terminated 1)  -- tag 18
  stopPx : Option (Terminated 1)  -- tag 99
  ordRejReason : Terminated 1  -- tag 103
  text : Option (Terminated 1)  -- tag 58
  securityExchange : Option (Terminated 1)  -- tag 207
  symbol : Terminated 1  -- tag 55
  qtyType : Option (Terminated 1)  -- tag 854
  contractMultiplier : Option (Terminated 1)  -- tag 231
  avgPx : Option (Terminated 1)  -- tag 6
  displayQty : Option (Terminated 1)  -- tag 1138
  deribitAdvOrderType : Option (Terminated 1)  -- tag 100012
  volatility : Option (Terminated 1)  -- tag 1188
  peggedPrice : Option (Terminated 1)  -- tag 839
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  trdMatchID : Option (Terminated 1)  -- tag 880
  deribitLabel : Option (Terminated 1)  -- tag 100010
  deribitMMProtection : Option (Terminated 1)  -- tag 9008
  mMPGroup : Option (Terminated 1)  -- tag 9019
  quoteSetID : Option (Terminated 1)  -- tag 302
  quoteID : Option (Terminated 1)  -- tag 117
  quoteEntryID : Option (Terminated 1)  -- tag 299
  noFills : List NoFills  -- tag 1362

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [51, 55] record.orderId,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdId,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 50] record.commission,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 53, 50] record.cashOrderQty,
   Part.optional [53, 49, 50, 55] record.conditionTriggerMethod,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 57] record.stopPx,
   Part.required [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.required [53, 53] record.symbol,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType,
   Part.optional [49, 49, 56, 56] record.volatility,
   Part.optional [56, 51, 57] record.peggedPrice,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [57, 48, 48, 56] record.deribitMMProtection,
   Part.optional [57, 48, 49, 57] record.mMPGroup,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [49, 49, 55] record.quoteID,
   Part.optional [50, 57, 57] record.quoteEntryID,
   Part.group [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within record.noFills]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[53, 50, 55]], [[51, 55]], [[49, 49]], [[52, 49]], [[51, 57]], [[53, 52]], [[54, 48]], [[49, 50]], [[49, 53, 49]], [[49, 52]], [[51, 56]], [[49, 53, 50]], [[53, 49, 50, 55]], [[52, 48]], [[52, 52]], [[49, 53, 48]], [[49, 56]], [[57, 57]], [[49, 48, 51]], [[53, 56]], [[50, 48, 55]], [[53, 53]], [[56, 53, 52]], [[50, 51, 49]], [[54]], [[49, 49, 51, 56]], [[49, 48, 48, 48, 49, 50]], [[49, 49, 56, 56]], [[56, 51, 57]], [[51, 49]], [[51, 50]], [[56, 56, 48]], [[49, 48, 48, 48, 49, 48]], [[57, 48, 48, 56]], [[57, 48, 49, 57]], [[51, 48, 50]], [[49, 49, 55]], [[50, 57, 57]], [49, 51, 54, 50] :: NoFills.members]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let orderId ← readOptional [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let commission ← readOptional [49, 50] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let cashOrderQty ← readOptional [49, 53, 50] tokens
  let conditionTriggerMethod ← readOptional [53, 49, 50, 55] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let execInst ← readOptional [49, 56] tokens
  let stopPx ← readOptional [57, 57] tokens
  let ordRejReason ← readRequired [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let avgPx ← readOptional [54] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let deribitAdvOrderType ← readOptional [49, 48, 48, 48, 49, 50] tokens
  let volatility ← readOptional [49, 49, 56, 56] tokens
  let peggedPrice ← readOptional [56, 51, 57] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let deribitMMProtection ← readOptional [57, 48, 48, 56] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteEntryID ← readOptional [50, 57, 57] tokens
  let noFills ← readGroup [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.decode tokens
  pure { secondaryExecID, orderId, clOrdID, origClOrdId, ordStatus, side, transactTime, commission, leavesQty, cumQty, orderQty, cashOrderQty, conditionTriggerMethod, ordType, price, execType, execInst, stopPx, ordRejReason, text, securityExchange, symbol, qtyType, contractMultiplier, avgPx, displayQty, deribitAdvOrderType, volatility, peggedPrice, lastPx, lastQty, trdMatchID, deribitLabel, deribitMMProtection, mMPGroup, quoteSetID, quoteID, quoteEntryID, noFills }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have cashOrderQty := readOptional_part [49, 53, 50] record.cashOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have conditionTriggerMethod := readOptional_part [53, 49, 50, 55] record.conditionTriggerMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have deribitAdvOrderType := readOptional_part [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have volatility := readOptional_part [49, 49, 56, 56] record.volatility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have peggedPrice := readOptional_part [56, 51, 57] record.peggedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have deribitMMProtection := readOptional_part [57, 48, 48, 56] record.deribitMMProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have quoteEntryID := readOptional_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have noFills := readGroup_part [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.encode NoFills.within NoFills.decode NoFills.decode_encode NoFills.led record.noFills tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  simp only [ExecutionReport.decode, secondaryExecID, orderId, clOrdID, origClOrdId, ordStatus, side, transactTime, commission, leavesQty, cumQty, orderQty, cashOrderQty, conditionTriggerMethod, ordType, price, execType, execInst, stopPx, ordRejReason, text, securityExchange, symbol, qtyType, contractMultiplier, avgPx, displayQty, deribitAdvOrderType, volatility, peggedPrice, lastPx, lastQty, trdMatchID, deribitLabel, deribitMMProtection, mMPGroup, quoteSetID, quoteID, quoteEntryID, noFills, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 50, 55] record.secondaryExecID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 50] record.commission (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50] record.cashOrderQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 49, 50, 55] record.conditionTriggerMethod (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [56, 53, 52] record.qtyType (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [54] record.avgPx (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 56, 56] record.volatility (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [56, 51, 57] record.peggedPrice (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 56] record.deribitMMProtection (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [49, 49, 55] record.quoteID (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [50, 57, 57] record.quoteEntryID (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_group pairing [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within (by decide) (by decide) NoFills.taken record.noFills)
                                         (paired_none pairing)))))))))))))))))))))))))))))))))))))))

structure Heartbeat where
  testReqId : Option (Terminated 1)  -- tag 112

def Heartbeat.parts (record : Heartbeat) : List Part :=
  [Part.optional [49, 49, 50] record.testReqId]

def Heartbeat.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (tokens : List Token) : Option Heartbeat := do
  let testReqId ← readOptional [49, 49, 50] tokens
  pure { testReqId }

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (agrees : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  have distinct : Heartbeat.tags.flatten.Nodup := by decide +kernel
  have testReqId := readOptional_part [49, 49, 50] record.testReqId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Heartbeat.decode, testReqId, some_bind] <;> rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqId (by decide) (by decide))
   (paired_none pairing)

structure Logon where
  heartBtInt : Terminated 1  -- tag 108
  rawData : List UInt8  -- tag 96
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  useWordsafeTags : Option (Terminated 1)  -- tag 9002
  cancelOnDisconnect : Option (Terminated 1)  -- tag 9001
  deribitAppId : Option (Terminated 1)  -- tag 9004
  deribitAppSig : Option (Terminated 1)  -- tag 9005
  deribitSequential : Option (Terminated 1)  -- tag 9007
  unsubscribeExecutionReports : Option (Terminated 1)  -- tag 9009
  connectionOnlyExecutionReports : Option (Terminated 1)  -- tag 9010
  reportFillsAsExecReports : Option (Terminated 1)  -- tag 9015
  displayIncrementSteps : Option (Terminated 1)  -- tag 9018

def Logon.parts (record : Logon) : List Part :=
  [Part.required [49, 48, 56] record.heartBtInt,
   Part.dataRequired [57, 53] [57, 54] record.rawData,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 48, 48, 50] record.useWordsafeTags,
   Part.optional [57, 48, 48, 49] record.cancelOnDisconnect,
   Part.optional [57, 48, 48, 52] record.deribitAppId,
   Part.optional [57, 48, 48, 53] record.deribitAppSig,
   Part.optional [57, 48, 48, 55] record.deribitSequential,
   Part.optional [57, 48, 48, 57] record.unsubscribeExecutionReports,
   Part.optional [57, 48, 49, 48] record.connectionOnlyExecutionReports,
   Part.optional [57, 48, 49, 53] record.reportFillsAsExecReports,
   Part.optional [57, 48, 49, 56] record.displayIncrementSteps]

def Logon.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]], [[57, 53], [57, 54]], [[53, 53, 51]], [[53, 53, 52]], [[57, 48, 48, 50]], [[57, 48, 48, 49]], [[57, 48, 48, 52]], [[57, 48, 48, 53]], [[57, 48, 48, 55]], [[57, 48, 48, 57]], [[57, 48, 49, 48]], [[57, 48, 49, 53]], [[57, 48, 49, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawData ← readData [57, 53] [57, 54] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let useWordsafeTags ← readOptional [57, 48, 48, 50] tokens
  let cancelOnDisconnect ← readOptional [57, 48, 48, 49] tokens
  let deribitAppId ← readOptional [57, 48, 48, 52] tokens
  let deribitAppSig ← readOptional [57, 48, 48, 53] tokens
  let deribitSequential ← readOptional [57, 48, 48, 55] tokens
  let unsubscribeExecutionReports ← readOptional [57, 48, 48, 57] tokens
  let connectionOnlyExecutionReports ← readOptional [57, 48, 49, 48] tokens
  let reportFillsAsExecReports ← readOptional [57, 48, 49, 53] tokens
  let displayIncrementSteps ← readOptional [57, 48, 49, 56] tokens
  pure { heartBtInt, rawData, username, password, useWordsafeTags, cancelOnDisconnect, deribitAppId, deribitAppSig, deribitSequential, unsubscribeExecutionReports, connectionOnlyExecutionReports, reportFillsAsExecReports, displayIncrementSteps }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rawData := readData_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have useWordsafeTags := readOptional_part [57, 48, 48, 50] record.useWordsafeTags tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cancelOnDisconnect := readOptional_part [57, 48, 48, 49] record.cancelOnDisconnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deribitAppId := readOptional_part [57, 48, 48, 52] record.deribitAppId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deribitAppSig := readOptional_part [57, 48, 48, 53] record.deribitAppSig tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have deribitSequential := readOptional_part [57, 48, 48, 55] record.deribitSequential tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have unsubscribeExecutionReports := readOptional_part [57, 48, 48, 57] record.unsubscribeExecutionReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have connectionOnlyExecutionReports := readOptional_part [57, 48, 49, 48] record.connectionOnlyExecutionReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have reportFillsAsExecReports := readOptional_part [57, 48, 49, 53] record.reportFillsAsExecReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displayIncrementSteps := readOptional_part [57, 48, 49, 56] record.displayIncrementSteps tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [Logon.decode, heartBtInt, rawData, username, password, useWordsafeTags, cancelOnDisconnect, deribitAppId, deribitAppSig, deribitSequential, unsubscribeExecutionReports, connectionOnlyExecutionReports, reportFillsAsExecReports, displayIncrementSteps, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
   (paired_cons pairing _ _ (paired_dataRequired pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53, 52] record.password (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 50] record.useWordsafeTags (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 49] record.cancelOnDisconnect (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 52] record.deribitAppId (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 53] record.deribitAppSig (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 55] record.deribitSequential (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 57] record.unsubscribeExecutionReports (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 48] record.connectionOnlyExecutionReports (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 53] record.reportFillsAsExecReports (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 56] record.displayIncrementSteps (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure Logout where
  text : Option (Terminated 1)  -- tag 58
  dontCancelOnDisconnect : Option (Terminated 1)  -- tag 9003

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.optional [57, 48, 48, 51] record.dontCancelOnDisconnect]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[57, 48, 48, 51]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  let dontCancelOnDisconnect ← readOptional [57, 48, 48, 51] tokens
  pure { text, dontCancelOnDisconnect }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have dontCancelOnDisconnect := readOptional_part [57, 48, 48, 51] record.dontCancelOnDisconnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, text, dontCancelOnDisconnect, some_bind] <;> rfl

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 51] record.dontCancelOnDisconnect (by decide) (by decide))
    (paired_none pairing))

structure NoMDEntries where
  mDUpdateAction : Terminated 1  -- tag 279
  mDEntryType : Option (Terminated 1)  -- tag 269
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryDate : Option (Terminated 1)  -- tag 272
  deribitTradeId : Option (Terminated 1)  -- tag 100009
  side : Option (Terminated 1)  -- tag 54
  orderId : Option (Terminated 1)  -- tag 37
  secondaryOrderId : Option (Terminated 1)  -- tag 198
  ordStatus : Option (Terminated 1)  -- tag 39
  deribitLabel : Option (Terminated 1)  -- tag 100010
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  deribitLiquidation : Option (Terminated 1)  -- tag 100091
  trdMatchID : Option (Terminated 1)  -- tag 880

def NoMDEntries.parts (record : NoMDEntries) : List Part :=
  [Part.required [50, 55, 57] record.mDUpdateAction,
   Part.optional [50, 54, 57] record.mDEntryType,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 55, 50] record.mDEntryDate,
   Part.optional [49, 48, 48, 48, 48, 57] record.deribitTradeId,
   Part.optional [53, 52] record.side,
   Part.optional [51, 55] record.orderId,
   Part.optional [49, 57, 56] record.secondaryOrderId,
   Part.optional [51, 57] record.ordStatus,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 48, 48, 57, 49] record.deribitLiquidation,
   Part.optional [56, 56, 48] record.trdMatchID]

def NoMDEntries.tags : List (List (List UInt8)) :=
  [[[50, 55, 57]], [[50, 54, 57]], [[50, 55, 48]], [[50, 55, 49]], [[50, 55, 50]], [[49, 48, 48, 48, 48, 57]], [[53, 52]], [[51, 55]], [[49, 57, 56]], [[51, 57]], [[49, 48, 48, 48, 49, 48]], [[52, 52]], [[53, 56]], [[49, 48, 48, 48, 57, 49]], [[56, 56, 48]]]

theorem NoMDEntries.shape (record : NoMDEntries) : record.parts.map Part.tags = NoMDEntries.tags := rfl

def NoMDEntries.decode (tokens : List Token) : Option NoMDEntries := do
  let mDUpdateAction ← readRequired [50, 55, 57] tokens
  let mDEntryType ← readOptional [50, 54, 57] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryDate ← readOptional [50, 55, 50] tokens
  let deribitTradeId ← readOptional [49, 48, 48, 48, 48, 57] tokens
  let side ← readOptional [53, 52] tokens
  let orderId ← readOptional [51, 55] tokens
  let secondaryOrderId ← readOptional [49, 57, 56] tokens
  let ordStatus ← readOptional [51, 57] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let deribitLiquidation ← readOptional [49, 48, 48, 48, 57, 49] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  pure { mDUpdateAction, mDEntryType, mDEntryPx, mDEntrySize, mDEntryDate, deribitTradeId, side, orderId, secondaryOrderId, ordStatus, deribitLabel, price, text, deribitLiquidation, trdMatchID }

theorem NoMDEntries.decode_agrees (record : NoMDEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntries.decode tokens = some record := by
  have distinct : NoMDEntries.tags.flatten.Nodup := by decide +kernel
  have mDUpdateAction := readRequired_part [50, 55, 57] record.mDUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryType := readOptional_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have mDEntryDate := readOptional_part [50, 55, 50] record.mDEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deribitTradeId := readOptional_part [49, 48, 48, 48, 48, 57] record.deribitTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have secondaryOrderId := readOptional_part [49, 57, 56] record.secondaryOrderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have deribitLiquidation := readOptional_part [49, 48, 48, 48, 57, 49] record.deribitLiquidation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [NoMDEntries.decode, mDUpdateAction, mDEntryType, mDEntryPx, mDEntrySize, mDEntryDate, deribitTradeId, side, orderId, secondaryOrderId, ordStatus, deribitLabel, price, text, deribitLiquidation, trdMatchID, some_bind] <;> rfl

theorem NoMDEntries.taken (record : NoMDEntries) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 55, 57] record.mDUpdateAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48] record.mDEntryPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 55, 49] record.mDEntrySize (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 55, 50] record.mDEntryDate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 57] record.deribitTradeId (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderId (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 57, 49] record.deribitLiquidation (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

def NoMDEntries.members : List (List UInt8) := NoMDEntries.tags.flatten

def NoMDEntries.encode (entry : NoMDEntries) : List Token := encodeParts entry.parts

theorem NoMDEntries.decode_encode (entry : NoMDEntries) : NoMDEntries.decode entry.encode = some entry :=
  NoMDEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntries.within (entry : NoMDEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntries.shape] at this

theorem NoMDEntries.led (entry : NoMDEntries) : Lead [50, 55, 57] entry.encode :=
  lead_parts [50, 55, 57] entry.mDUpdateAction _ NoMDEntries.tags.tail rfl (by decide +kernel)

structure MarketDataIncrementalRefresh where
  symbol : Terminated 1  -- tag 55
  mDReqID : Option (Terminated 1)  -- tag 262
  contractMultiplier : Option (Terminated 1)  -- tag 231
  putOrCall : Option (Terminated 1)  -- tag 201
  tradeVolume24h : Option (Terminated 1)  -- tag 100087
  markPrice : Option (Terminated 1)  -- tag 100090
  openInterest : Option (Terminated 1)  -- tag 746
  noMDEntries : List NoMDEntries  -- tag 268

def MarketDataIncrementalRefresh.parts (record : MarketDataIncrementalRefresh) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [50, 54, 50] record.mDReqID,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [49, 48, 48, 48, 56, 55] record.tradeVolume24h,
   Part.optional [49, 48, 48, 48, 57, 48] record.markPrice,
   Part.optional [55, 52, 54] record.openInterest,
   Part.group [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within record.noMDEntries]

def MarketDataIncrementalRefresh.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[50, 54, 50]], [[50, 51, 49]], [[50, 48, 49]], [[49, 48, 48, 48, 56, 55]], [[49, 48, 48, 48, 57, 48]], [[55, 52, 54]], [50, 54, 56] :: NoMDEntries.members]

theorem MarketDataIncrementalRefresh.shape (record : MarketDataIncrementalRefresh) : record.parts.map Part.tags = MarketDataIncrementalRefresh.tags := rfl

def MarketDataIncrementalRefresh.decode (tokens : List Token) : Option MarketDataIncrementalRefresh := do
  let symbol ← readRequired [53, 53] tokens
  let mDReqID ← readOptional [50, 54, 50] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let tradeVolume24h ← readOptional [49, 48, 48, 48, 56, 55] tokens
  let markPrice ← readOptional [49, 48, 48, 48, 57, 48] tokens
  let openInterest ← readOptional [55, 52, 54] tokens
  let noMDEntries ← readGroup [50, 54, 56] [50, 55, 57] NoMDEntries.members NoMDEntries.decode tokens
  pure { symbol, mDReqID, contractMultiplier, putOrCall, tradeVolume24h, markPrice, openInterest, noMDEntries }

theorem MarketDataIncrementalRefresh.decode_agrees (record : MarketDataIncrementalRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataIncrementalRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataIncrementalRefresh.decode tokens = some record := by
  have distinct : MarketDataIncrementalRefresh.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDReqID := readOptional_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeVolume24h := readOptional_part [49, 48, 48, 48, 56, 55] record.tradeVolume24h tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have markPrice := readOptional_part [49, 48, 48, 48, 57, 48] record.markPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have openInterest := readOptional_part [55, 52, 54] record.openInterest tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noMDEntries := readGroup_part [50, 54, 56] [50, 55, 57] NoMDEntries.members NoMDEntries.encode NoMDEntries.within NoMDEntries.decode NoMDEntries.decode_encode NoMDEntries.led record.noMDEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [MarketDataIncrementalRefresh.decode, symbol, mDReqID, contractMultiplier, putOrCall, tradeVolume24h, markPrice, openInterest, noMDEntries, some_bind] <;> rfl

theorem MarketDataIncrementalRefresh.taken (record : MarketDataIncrementalRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 56, 55] record.tradeVolume24h (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 57, 48] record.markPrice (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [55, 52, 54] record.openInterest (by decide) (by decide))
         (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within (by decide) (by decide) NoMDEntries.taken record.noMDEntries)
          (paired_none pairing))))))))

structure MarketDataRequestReject where
  text : Option (Terminated 1)  -- tag 58
  mDReqID : Terminated 1  -- tag 262
  mDReqRejReason : Terminated 1  -- tag 281

def MarketDataRequestReject.parts (record : MarketDataRequestReject) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 56, 49] record.mDReqRejReason]

def MarketDataRequestReject.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[50, 54, 50]], [[50, 56, 49]]]

theorem MarketDataRequestReject.shape (record : MarketDataRequestReject) : record.parts.map Part.tags = MarketDataRequestReject.tags := rfl

def MarketDataRequestReject.decode (tokens : List Token) : Option MarketDataRequestReject := do
  let text ← readOptional [53, 56] tokens
  let mDReqID ← readRequired [50, 54, 50] tokens
  let mDReqRejReason ← readRequired [50, 56, 49] tokens
  pure { text, mDReqID, mDReqRejReason }

theorem MarketDataRequestReject.decode_agrees (record : MarketDataRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequestReject.decode tokens = some record := by
  have distinct : MarketDataRequestReject.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDReqRejReason := readRequired_part [50, 56, 49] record.mDReqRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [MarketDataRequestReject.decode, text, mDReqID, mDReqRejReason, some_bind] <;> rfl

theorem MarketDataRequestReject.taken (record : MarketDataRequestReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 56, 49] record.mDReqRejReason (by decide) (by decide))
     (paired_none pairing)))

structure MarketDataSnapshot where
  symbol : Terminated 1  -- tag 55
  mDReqID : Option (Terminated 1)  -- tag 262
  underlyingSymbol : Option (Terminated 1)  -- tag 311
  underlyingPx : Option (Terminated 1)  -- tag 810
  contractMultiplier : Option (Terminated 1)  -- tag 231
  putOrCall : Option (Terminated 1)  -- tag 201
  tradeVolume24h : Option (Terminated 1)  -- tag 100087
  markPrice : Option (Terminated 1)  -- tag 100090
  openInterest : Option (Terminated 1)  -- tag 746
  currentFunding : Option (Terminated 1)  -- tag 100092
  funding8h : Option (Terminated 1)  -- tag 100093
  noMDEntries : List NoMDEntries  -- tag 268

def MarketDataSnapshot.parts (record : MarketDataSnapshot) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [50, 54, 50] record.mDReqID,
   Part.optional [51, 49, 49] record.underlyingSymbol,
   Part.optional [56, 49, 48] record.underlyingPx,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [49, 48, 48, 48, 56, 55] record.tradeVolume24h,
   Part.optional [49, 48, 48, 48, 57, 48] record.markPrice,
   Part.optional [55, 52, 54] record.openInterest,
   Part.optional [49, 48, 48, 48, 57, 50] record.currentFunding,
   Part.optional [49, 48, 48, 48, 57, 51] record.funding8h,
   Part.group [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within record.noMDEntries]

def MarketDataSnapshot.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[50, 54, 50]], [[51, 49, 49]], [[56, 49, 48]], [[50, 51, 49]], [[50, 48, 49]], [[49, 48, 48, 48, 56, 55]], [[49, 48, 48, 48, 57, 48]], [[55, 52, 54]], [[49, 48, 48, 48, 57, 50]], [[49, 48, 48, 48, 57, 51]], [50, 54, 56] :: NoMDEntries.members]

theorem MarketDataSnapshot.shape (record : MarketDataSnapshot) : record.parts.map Part.tags = MarketDataSnapshot.tags := rfl

def MarketDataSnapshot.decode (tokens : List Token) : Option MarketDataSnapshot := do
  let symbol ← readRequired [53, 53] tokens
  let mDReqID ← readOptional [50, 54, 50] tokens
  let underlyingSymbol ← readOptional [51, 49, 49] tokens
  let underlyingPx ← readOptional [56, 49, 48] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let tradeVolume24h ← readOptional [49, 48, 48, 48, 56, 55] tokens
  let markPrice ← readOptional [49, 48, 48, 48, 57, 48] tokens
  let openInterest ← readOptional [55, 52, 54] tokens
  let currentFunding ← readOptional [49, 48, 48, 48, 57, 50] tokens
  let funding8h ← readOptional [49, 48, 48, 48, 57, 51] tokens
  let noMDEntries ← readGroup [50, 54, 56] [50, 55, 57] NoMDEntries.members NoMDEntries.decode tokens
  pure { symbol, mDReqID, underlyingSymbol, underlyingPx, contractMultiplier, putOrCall, tradeVolume24h, markPrice, openInterest, currentFunding, funding8h, noMDEntries }

theorem MarketDataSnapshot.decode_agrees (record : MarketDataSnapshot) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataSnapshot.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataSnapshot.decode tokens = some record := by
  have distinct : MarketDataSnapshot.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDReqID := readOptional_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have underlyingSymbol := readOptional_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have underlyingPx := readOptional_part [56, 49, 48] record.underlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have tradeVolume24h := readOptional_part [49, 48, 48, 48, 56, 55] record.tradeVolume24h tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have markPrice := readOptional_part [49, 48, 48, 48, 57, 48] record.markPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have openInterest := readOptional_part [55, 52, 54] record.openInterest tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have currentFunding := readOptional_part [49, 48, 48, 48, 57, 50] record.currentFunding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have funding8h := readOptional_part [49, 48, 48, 48, 57, 51] record.funding8h tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noMDEntries := readGroup_part [50, 54, 56] [50, 55, 57] NoMDEntries.members NoMDEntries.encode NoMDEntries.within NoMDEntries.decode NoMDEntries.decode_encode NoMDEntries.led record.noMDEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [MarketDataSnapshot.decode, symbol, mDReqID, underlyingSymbol, underlyingPx, contractMultiplier, putOrCall, tradeVolume24h, markPrice, openInterest, currentFunding, funding8h, noMDEntries, some_bind] <;> rfl

theorem MarketDataSnapshot.taken (record : MarketDataSnapshot) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [56, 49, 48] record.underlyingPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 56, 55] record.tradeVolume24h (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 57, 48] record.markPrice (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 52, 54] record.openInterest (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 57, 50] record.currentFunding (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 57, 51] record.funding8h (by decide) (by decide))
             (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within (by decide) (by decide) NoMDEntries.taken record.noMDEntries)
              (paired_none pairing))))))))))))

structure NoQuoteEntries where
  quoteEntryID : Terminated 1  -- tag 299
  quoteEntryType : Option (Terminated 1)  -- tag 9020
  quoteSetID : Option (Terminated 1)  -- tag 302
  quoteEntryStatus : Option (Terminated 1)  -- tag 1167
  symbol : Option (Terminated 1)  -- tag 55
  side : Option (Terminated 1)  -- tag 54
  orderQty2 : Option (Terminated 1)  -- tag 192
  orderId : Option (Terminated 1)  -- tag 37
  transactTime : Option (Terminated 1)  -- tag 60
  bidPx : Option (Terminated 1)  -- tag 132
  bidSize : Option (Terminated 1)  -- tag 134
  offerPx : Option (Terminated 1)  -- tag 133
  offerSize : Option (Terminated 1)  -- tag 135
  quoteEntryRejectReason : Option (Terminated 1)  -- tag 368
  text : Option (Terminated 1)  -- tag 58

def NoQuoteEntries.parts (record : NoQuoteEntries) : List Part :=
  [Part.required [50, 57, 57] record.quoteEntryID,
   Part.optional [57, 48, 50, 48] record.quoteEntryType,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [49, 49, 54, 55] record.quoteEntryStatus,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 52] record.side,
   Part.optional [49, 57, 50] record.orderQty2,
   Part.optional [51, 55] record.orderId,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [51, 54, 56] record.quoteEntryRejectReason,
   Part.optional [53, 56] record.text]

def NoQuoteEntries.tags : List (List (List UInt8)) :=
  [[[50, 57, 57]], [[57, 48, 50, 48]], [[51, 48, 50]], [[49, 49, 54, 55]], [[53, 53]], [[53, 52]], [[49, 57, 50]], [[51, 55]], [[54, 48]], [[49, 51, 50]], [[49, 51, 52]], [[49, 51, 51]], [[49, 51, 53]], [[51, 54, 56]], [[53, 56]]]

theorem NoQuoteEntries.shape (record : NoQuoteEntries) : record.parts.map Part.tags = NoQuoteEntries.tags := rfl

def NoQuoteEntries.decode (tokens : List Token) : Option NoQuoteEntries := do
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let quoteEntryType ← readOptional [57, 48, 50, 48] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let quoteEntryStatus ← readOptional [49, 49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let side ← readOptional [53, 52] tokens
  let orderQty2 ← readOptional [49, 57, 50] tokens
  let orderId ← readOptional [51, 55] tokens
  let transactTime ← readOptional [54, 48] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let quoteEntryRejectReason ← readOptional [51, 54, 56] tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteEntryID, quoteEntryType, quoteSetID, quoteEntryStatus, symbol, side, orderQty2, orderId, transactTime, bidPx, bidSize, offerPx, offerSize, quoteEntryRejectReason, text }

theorem NoQuoteEntries.decode_agrees (record : NoQuoteEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteEntries.decode tokens = some record := by
  have distinct : NoQuoteEntries.tags.flatten.Nodup := by decide +kernel
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteEntryType := readOptional_part [57, 48, 50, 48] record.quoteEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteEntryStatus := readOptional_part [49, 49, 54, 55] record.quoteEntryStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderQty2 := readOptional_part [49, 57, 50] record.orderQty2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have quoteEntryRejectReason := readOptional_part [51, 54, 56] record.quoteEntryRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [NoQuoteEntries.decode, quoteEntryID, quoteEntryType, quoteSetID, quoteEntryStatus, symbol, side, orderQty2, orderId, transactTime, bidPx, bidSize, offerPx, offerSize, quoteEntryRejectReason, text, some_bind] <;> rfl

theorem NoQuoteEntries.taken (record : NoQuoteEntries) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 57, 57] record.quoteEntryID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 50, 48] record.quoteEntryType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54, 55] record.quoteEntryStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 57, 50] record.orderQty2 (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50] record.bidPx (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 51, 52] record.bidSize (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 51, 51] record.offerPx (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 51, 53] record.offerSize (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 54, 56] record.quoteEntryRejectReason (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

def NoQuoteEntries.members : List (List UInt8) := NoQuoteEntries.tags.flatten

def NoQuoteEntries.encode (entry : NoQuoteEntries) : List Token := encodeParts entry.parts

theorem NoQuoteEntries.decode_encode (entry : NoQuoteEntries) : NoQuoteEntries.decode entry.encode = some entry :=
  NoQuoteEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteEntries.within (entry : NoQuoteEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteEntries.shape] at this

theorem NoQuoteEntries.led (entry : NoQuoteEntries) : Lead [50, 57, 57] entry.encode :=
  lead_parts [50, 57, 57] entry.quoteEntryID _ NoQuoteEntries.tags.tail rfl (by decide +kernel)

structure MassQuoteAcknowledgement where
  quoteID : Option (Terminated 1)  -- tag 117
  quoteStatus : Terminated 1  -- tag 297
  quoteRejectReason : Option (Terminated 1)  -- tag 300
  noQuoteEntries : List NoQuoteEntries  -- tag 295

def MassQuoteAcknowledgement.parts (record : MassQuoteAcknowledgement) : List Part :=
  [Part.optional [49, 49, 55] record.quoteID,
   Part.required [50, 57, 55] record.quoteStatus,
   Part.optional [51, 48, 48] record.quoteRejectReason,
   Part.group [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within record.noQuoteEntries]

def MassQuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[50, 57, 55]], [[51, 48, 48]], [50, 57, 53] :: NoQuoteEntries.members]

theorem MassQuoteAcknowledgement.shape (record : MassQuoteAcknowledgement) : record.parts.map Part.tags = MassQuoteAcknowledgement.tags := rfl

def MassQuoteAcknowledgement.decode (tokens : List Token) : Option MassQuoteAcknowledgement := do
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteStatus ← readRequired [50, 57, 55] tokens
  let quoteRejectReason ← readOptional [51, 48, 48] tokens
  let noQuoteEntries ← readGroup [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.decode tokens
  pure { quoteID, quoteStatus, quoteRejectReason, noQuoteEntries }

theorem MassQuoteAcknowledgement.decode_agrees (record : MassQuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuoteAcknowledgement.decode tokens = some record := by
  have distinct : MassQuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteStatus := readRequired_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have quoteRejectReason := readOptional_part [51, 48, 48] record.quoteRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noQuoteEntries := readGroup_part [50, 57, 53] [50, 57, 57] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within NoQuoteEntries.decode NoQuoteEntries.decode_encode NoQuoteEntries.led record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [MassQuoteAcknowledgement.decode, quoteID, quoteStatus, quoteRejectReason, noQuoteEntries, some_bind] <;> rfl

theorem MassQuoteAcknowledgement.taken (record : MassQuoteAcknowledgement) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 57, 55] record.quoteStatus (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48] record.quoteRejectReason (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [50, 57, 53] NoQuoteEntries.members NoQuoteEntries.encode NoQuoteEntries.within (by decide) (by decide) NoQuoteEntries.taken record.noQuoteEntries)
      (paired_none pairing))))

structure MMProtectionLimitsResult where
  protectionRequestID : Terminated 1  -- tag 20114
  protectionRequestResult : Terminated 1  -- tag 20117
  text : Option (Terminated 1)  -- tag 58

def MMProtectionLimitsResult.parts (record : MMProtectionLimitsResult) : List Part :=
  [Part.required [50, 48, 49, 49, 52] record.protectionRequestID,
   Part.required [50, 48, 49, 49, 55] record.protectionRequestResult,
   Part.optional [53, 56] record.text]

def MMProtectionLimitsResult.tags : List (List (List UInt8)) :=
  [[[50, 48, 49, 49, 52]], [[50, 48, 49, 49, 55]], [[53, 56]]]

theorem MMProtectionLimitsResult.shape (record : MMProtectionLimitsResult) : record.parts.map Part.tags = MMProtectionLimitsResult.tags := rfl

def MMProtectionLimitsResult.decode (tokens : List Token) : Option MMProtectionLimitsResult := do
  let protectionRequestID ← readRequired [50, 48, 49, 49, 52] tokens
  let protectionRequestResult ← readRequired [50, 48, 49, 49, 55] tokens
  let text ← readOptional [53, 56] tokens
  pure { protectionRequestID, protectionRequestResult, text }

theorem MMProtectionLimitsResult.decode_agrees (record : MMProtectionLimitsResult) (tokens : List Token)
    (agrees : ∀ tags ∈ MMProtectionLimitsResult.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MMProtectionLimitsResult.decode tokens = some record := by
  have distinct : MMProtectionLimitsResult.tags.flatten.Nodup := by decide +kernel
  have protectionRequestID := readRequired_part [50, 48, 49, 49, 52] record.protectionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have protectionRequestResult := readRequired_part [50, 48, 49, 49, 55] record.protectionRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [MMProtectionLimitsResult.decode, protectionRequestID, protectionRequestResult, text, some_bind] <;> rfl

theorem MMProtectionLimitsResult.taken (record : MMProtectionLimitsResult) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 52] record.protectionRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 55] record.protectionRequestResult (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_none pairing)))

structure OrderCancelReject where
  ordStatus : Option (Terminated 1)  -- tag 39
  text : Option (Terminated 1)  -- tag 58
  origClOrdId : Option (Terminated 1)  -- tag 41
  clOrdID : Option (Terminated 1)  -- tag 11
  deribitLabel : Option (Terminated 1)  -- tag 100010
  execType : Option (Terminated 1)  -- tag 150

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.optional [51, 57] record.ordStatus,
   Part.optional [53, 56] record.text,
   Part.optional [52, 49] record.origClOrdId,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [49, 53, 48] record.execType]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 57]], [[53, 56]], [[52, 49]], [[49, 49]], [[49, 48, 48, 48, 49, 48]], [[49, 53, 48]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let ordStatus ← readOptional [51, 57] tokens
  let text ← readOptional [53, 56] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let execType ← readOptional [49, 53, 48] tokens
  pure { ordStatus, text, origClOrdId, clOrdID, deribitLabel, execType }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderCancelReject.decode, ordStatus, text, origClOrdId, clOrdID, deribitLabel, execType, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 57] record.ordStatus (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
        (paired_none pairing))))))

structure NoAffectedOrders where
  origClOrdId : Terminated 1  -- tag 41

def NoAffectedOrders.parts (record : NoAffectedOrders) : List Part :=
  [Part.required [52, 49] record.origClOrdId]

def NoAffectedOrders.tags : List (List (List UInt8)) :=
  [[[52, 49]]]

theorem NoAffectedOrders.shape (record : NoAffectedOrders) : record.parts.map Part.tags = NoAffectedOrders.tags := rfl

def NoAffectedOrders.decode (tokens : List Token) : Option NoAffectedOrders := do
  let origClOrdId ← readRequired [52, 49] tokens
  pure { origClOrdId }

theorem NoAffectedOrders.decode_agrees (record : NoAffectedOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAffectedOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAffectedOrders.decode tokens = some record := by
  have distinct : NoAffectedOrders.tags.flatten.Nodup := by decide +kernel
  have origClOrdId := readRequired_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoAffectedOrders.decode, origClOrdId, some_bind] <;> rfl

theorem NoAffectedOrders.taken (record : NoAffectedOrders) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdId (by decide) (by decide))
   (paired_none pairing)

def NoAffectedOrders.members : List (List UInt8) := NoAffectedOrders.tags.flatten

def NoAffectedOrders.encode (entry : NoAffectedOrders) : List Token := encodeParts entry.parts

theorem NoAffectedOrders.decode_encode (entry : NoAffectedOrders) : NoAffectedOrders.decode entry.encode = some entry :=
  NoAffectedOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAffectedOrders.within (entry : NoAffectedOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoAffectedOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAffectedOrders.shape] at this

theorem NoAffectedOrders.led (entry : NoAffectedOrders) : Lead [52, 49] entry.encode :=
  lead_parts [52, 49] entry.origClOrdId _ NoAffectedOrders.tags.tail rfl (by decide +kernel)

structure OrderMassCancelReport where
  clOrdID : Option (Terminated 1)  -- tag 11
  orderId : Option (Terminated 1)  -- tag 37
  massCancelRequestType : Terminated 1  -- tag 530
  massCancelResponse : Option (Terminated 1)  -- tag 531
  quoteCancelType : Option (Terminated 1)  -- tag 298
  text : Option (Terminated 1)  -- tag 58
  massCancelRejectReason : Option (Terminated 1)  -- tag 532
  totalAffectedOrders : Option (Terminated 1)  -- tag 533
  noAffectedOrders : List NoAffectedOrders  -- tag 534

def OrderMassCancelReport.parts (record : OrderMassCancelReport) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderId,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [53, 51, 49] record.massCancelResponse,
   Part.optional [50, 57, 56] record.quoteCancelType,
   Part.optional [53, 56] record.text,
   Part.optional [53, 51, 50] record.massCancelRejectReason,
   Part.optional [53, 51, 51] record.totalAffectedOrders,
   Part.group [53, 51, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within record.noAffectedOrders]

def OrderMassCancelReport.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 51, 48]], [[53, 51, 49]], [[50, 57, 56]], [[53, 56]], [[53, 51, 50]], [[53, 51, 51]], [53, 51, 52] :: NoAffectedOrders.members]

theorem OrderMassCancelReport.shape (record : OrderMassCancelReport) : record.parts.map Part.tags = OrderMassCancelReport.tags := rfl

def OrderMassCancelReport.decode (tokens : List Token) : Option OrderMassCancelReport := do
  let clOrdID ← readOptional [49, 49] tokens
  let orderId ← readOptional [51, 55] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let massCancelResponse ← readOptional [53, 51, 49] tokens
  let quoteCancelType ← readOptional [50, 57, 56] tokens
  let text ← readOptional [53, 56] tokens
  let massCancelRejectReason ← readOptional [53, 51, 50] tokens
  let totalAffectedOrders ← readOptional [53, 51, 51] tokens
  let noAffectedOrders ← readGroup [53, 51, 52] [52, 49] NoAffectedOrders.members NoAffectedOrders.decode tokens
  pure { clOrdID, orderId, massCancelRequestType, massCancelResponse, quoteCancelType, text, massCancelRejectReason, totalAffectedOrders, noAffectedOrders }

theorem OrderMassCancelReport.decode_agrees (record : OrderMassCancelReport) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelReport.decode tokens = some record := by
  have distinct : OrderMassCancelReport.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have massCancelResponse := readOptional_part [53, 51, 49] record.massCancelResponse tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have quoteCancelType := readOptional_part [50, 57, 56] record.quoteCancelType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have massCancelRejectReason := readOptional_part [53, 51, 50] record.massCancelRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have totalAffectedOrders := readOptional_part [53, 51, 51] record.totalAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noAffectedOrders := readGroup_part [53, 51, 52] [52, 49] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within NoAffectedOrders.decode NoAffectedOrders.decode_encode NoAffectedOrders.led record.noAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [OrderMassCancelReport.decode, clOrdID, orderId, massCancelRequestType, massCancelResponse, quoteCancelType, text, massCancelRejectReason, totalAffectedOrders, noAffectedOrders, some_bind] <;> rfl

theorem OrderMassCancelReport.taken (record : OrderMassCancelReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.massCancelRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 51, 49] record.massCancelResponse (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 57, 56] record.quoteCancelType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 51, 50] record.massCancelRejectReason (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 51, 51] record.totalAffectedOrders (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [53, 51, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within (by decide) (by decide) NoAffectedOrders.taken record.noAffectedOrders)
           (paired_none pairing)))))))))

structure NoPositions where
  posType : Terminated 1  -- tag 703
  longQty : Option (Terminated 1)  -- tag 704
  shortQty : Option (Terminated 1)  -- tag 705
  symbol : Option (Terminated 1)  -- tag 55
  qtyType : Option (Terminated 1)  -- tag 854
  contractMultiplier : Option (Terminated 1)  -- tag 231
  underlyingEndPrice : Option (Terminated 1)  -- tag 883
  side : Option (Terminated 1)  -- tag 54
  settlPrice : Option (Terminated 1)  -- tag 730
  rawData : Option (List UInt8)  -- tag 96
  deribitLiquidationPrice : Option (Terminated 1)  -- tag 100088
  deribitSizeInCurrency : Option (Terminated 1)  -- tag 100089

def NoPositions.parts (record : NoPositions) : List Part :=
  [Part.required [55, 48, 51] record.posType,
   Part.optional [55, 48, 52] record.longQty,
   Part.optional [55, 48, 53] record.shortQty,
   Part.optional [53, 53] record.symbol,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [56, 56, 51] record.underlyingEndPrice,
   Part.optional [53, 52] record.side,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.dataOptional [57, 53] [57, 54] record.rawData,
   Part.optional [49, 48, 48, 48, 56, 56] record.deribitLiquidationPrice,
   Part.optional [49, 48, 48, 48, 56, 57] record.deribitSizeInCurrency]

def NoPositions.tags : List (List (List UInt8)) :=
  [[[55, 48, 51]], [[55, 48, 52]], [[55, 48, 53]], [[53, 53]], [[56, 53, 52]], [[50, 51, 49]], [[56, 56, 51]], [[53, 52]], [[55, 51, 48]], [[57, 53], [57, 54]], [[49, 48, 48, 48, 56, 56]], [[49, 48, 48, 48, 56, 57]]]

theorem NoPositions.shape (record : NoPositions) : record.parts.map Part.tags = NoPositions.tags := rfl

def NoPositions.decode (tokens : List Token) : Option NoPositions := do
  let posType ← readRequired [55, 48, 51] tokens
  let longQty ← readOptional [55, 48, 52] tokens
  let shortQty ← readOptional [55, 48, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let underlyingEndPrice ← readOptional [56, 56, 51] tokens
  let side ← readOptional [53, 52] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  let deribitLiquidationPrice ← readOptional [49, 48, 48, 48, 56, 56] tokens
  let deribitSizeInCurrency ← readOptional [49, 48, 48, 48, 56, 57] tokens
  pure { posType, longQty, shortQty, symbol, qtyType, contractMultiplier, underlyingEndPrice, side, settlPrice, rawData, deribitLiquidationPrice, deribitSizeInCurrency }

theorem NoPositions.decode_agrees (record : NoPositions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPositions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPositions.decode tokens = some record := by
  have distinct : NoPositions.tags.flatten.Nodup := by decide +kernel
  have posType := readRequired_part [55, 48, 51] record.posType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have longQty := readOptional_part [55, 48, 52] record.longQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have shortQty := readOptional_part [55, 48, 53] record.shortQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have underlyingEndPrice := readOptional_part [56, 56, 51] record.underlyingEndPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have rawData := readDataOptional_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deribitLiquidationPrice := readOptional_part [49, 48, 48, 48, 56, 56] record.deribitLiquidationPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deribitSizeInCurrency := readOptional_part [49, 48, 48, 48, 56, 57] record.deribitSizeInCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [NoPositions.decode, posType, longQty, shortQty, symbol, qtyType, contractMultiplier, underlyingEndPrice, side, settlPrice, rawData, deribitLiquidationPrice, deribitSizeInCurrency, some_bind] <;> rfl

theorem NoPositions.taken (record : NoPositions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55, 48, 51] record.posType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [55, 48, 52] record.longQty (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [55, 48, 53] record.shortQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [56, 53, 52] record.qtyType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [56, 56, 51] record.underlyingEndPrice (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 51, 48] record.settlPrice (by decide) (by decide))
           (paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 56, 56] record.deribitLiquidationPrice (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 56, 57] record.deribitSizeInCurrency (by decide) (by decide))
              (paired_none pairing))))))))))))

def NoPositions.members : List (List UInt8) := NoPositions.tags.flatten

def NoPositions.encode (entry : NoPositions) : List Token := encodeParts entry.parts

theorem NoPositions.decode_encode (entry : NoPositions) : NoPositions.decode entry.encode = some entry :=
  NoPositions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPositions.within (entry : NoPositions) : ∀ token ∈ entry.encode, token.tag ∈ NoPositions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPositions.shape] at this

theorem NoPositions.led (entry : NoPositions) : Lead [55, 48, 51] entry.encode :=
  lead_parts [55, 48, 51] entry.posType _ NoPositions.tags.tail rfl (by decide +kernel)

structure PositionReport where
  posMaintRptID : Terminated 1  -- tag 721
  posReqID : Option (Terminated 1)  -- tag 710
  posReqType : Option (Terminated 1)  -- tag 724
  posReqResult : Option (Terminated 1)  -- tag 728
  noPositions : List NoPositions  -- tag 702

def PositionReport.parts (record : PositionReport) : List Part :=
  [Part.required [55, 50, 49] record.posMaintRptID,
   Part.optional [55, 49, 48] record.posReqID,
   Part.optional [55, 50, 52] record.posReqType,
   Part.optional [55, 50, 56] record.posReqResult,
   Part.group [55, 48, 50] NoPositions.members NoPositions.encode NoPositions.within record.noPositions]

def PositionReport.tags : List (List (List UInt8)) :=
  [[[55, 50, 49]], [[55, 49, 48]], [[55, 50, 52]], [[55, 50, 56]], [55, 48, 50] :: NoPositions.members]

theorem PositionReport.shape (record : PositionReport) : record.parts.map Part.tags = PositionReport.tags := rfl

def PositionReport.decode (tokens : List Token) : Option PositionReport := do
  let posMaintRptID ← readRequired [55, 50, 49] tokens
  let posReqID ← readOptional [55, 49, 48] tokens
  let posReqType ← readOptional [55, 50, 52] tokens
  let posReqResult ← readOptional [55, 50, 56] tokens
  let noPositions ← readGroup [55, 48, 50] [55, 48, 51] NoPositions.members NoPositions.decode tokens
  pure { posMaintRptID, posReqID, posReqType, posReqResult, noPositions }

theorem PositionReport.decode_agrees (record : PositionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ PositionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PositionReport.decode tokens = some record := by
  have distinct : PositionReport.tags.flatten.Nodup := by decide +kernel
  have posMaintRptID := readRequired_part [55, 50, 49] record.posMaintRptID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have posReqID := readOptional_part [55, 49, 48] record.posReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have posReqType := readOptional_part [55, 50, 52] record.posReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have posReqResult := readOptional_part [55, 50, 56] record.posReqResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noPositions := readGroup_part [55, 48, 50] [55, 48, 51] NoPositions.members NoPositions.encode NoPositions.within NoPositions.decode NoPositions.decode_encode NoPositions.led record.noPositions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [PositionReport.decode, posMaintRptID, posReqID, posReqType, posReqResult, noPositions, some_bind] <;> rfl

theorem PositionReport.taken (record : PositionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55, 50, 49] record.posMaintRptID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [55, 49, 48] record.posReqID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [55, 50, 52] record.posReqType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 50, 56] record.posReqResult (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [55, 48, 50] NoPositions.members NoPositions.encode NoPositions.within (by decide) (by decide) NoPositions.taken record.noPositions)
       (paired_none pairing)))))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, sessionRejectReason, text }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

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

theorem ResendRequest.taken (record : ResendRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55] record.beginSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54] record.endSeqNo (by decide) (by decide))
    (paired_none pairing))

structure NoUnderlyings where
  underlyingSymbol : Terminated 1  -- tag 311

def NoUnderlyings.parts (record : NoUnderlyings) : List Part :=
  [Part.required [51, 49, 49] record.underlyingSymbol]

def NoUnderlyings.tags : List (List (List UInt8)) :=
  [[[51, 49, 49]]]

theorem NoUnderlyings.shape (record : NoUnderlyings) : record.parts.map Part.tags = NoUnderlyings.tags := rfl

def NoUnderlyings.decode (tokens : List Token) : Option NoUnderlyings := do
  let underlyingSymbol ← readRequired [51, 49, 49] tokens
  pure { underlyingSymbol }

theorem NoUnderlyings.decode_agrees (record : NoUnderlyings) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUnderlyings.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUnderlyings.decode tokens = some record := by
  have distinct : NoUnderlyings.tags.flatten.Nodup := by decide +kernel
  have underlyingSymbol := readRequired_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoUnderlyings.decode, underlyingSymbol, some_bind] <;> rfl

theorem NoUnderlyings.taken (record : NoUnderlyings) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
   (paired_none pairing)

def NoUnderlyings.members : List (List UInt8) := NoUnderlyings.tags.flatten

def NoUnderlyings.encode (entry : NoUnderlyings) : List Token := encodeParts entry.parts

theorem NoUnderlyings.decode_encode (entry : NoUnderlyings) : NoUnderlyings.decode entry.encode = some entry :=
  NoUnderlyings.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUnderlyings.within (entry : NoUnderlyings) : ∀ token ∈ entry.encode, token.tag ∈ NoUnderlyings.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUnderlyings.shape] at this

theorem NoUnderlyings.led (entry : NoUnderlyings) : Lead [51, 49, 49] entry.encode :=
  lead_parts [51, 49, 49] entry.underlyingSymbol _ NoUnderlyings.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSide : Option (Terminated 1)  -- tag 624
  legRatioQty : Option (Terminated 1)  -- tag 623

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [54, 50, 51] record.legRatioQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 50, 52]], [[54, 50, 51]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  pure { legSymbol, legSide, legRatioQty }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSide, legRatioQty, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 50, 52] record.legSide (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 50, 51] record.legRatioQty (by decide) (by decide))
     (paired_none pairing)))

def NoLegs.members : List (List UInt8) := NoLegs.tags.flatten

def NoLegs.encode (entry : NoLegs) : List Token := encodeParts entry.parts

theorem NoLegs.decode_encode (entry : NoLegs) : NoLegs.decode entry.encode = some entry :=
  NoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegs.within (entry : NoLegs) : ∀ token ∈ entry.encode, token.tag ∈ NoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegs.shape] at this

theorem NoLegs.led (entry : NoLegs) : Lead [54, 48, 48] entry.encode :=
  lead_parts [54, 48, 48] entry.legSymbol _ NoLegs.tags.tail rfl (by decide +kernel)

structure SecurityDefinition where
  securityReqID : Terminated 1  -- tag 320
  securityResponseID : Terminated 1  -- tag 322
  securityResponseType : Terminated 1  -- tag 323
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  issueDate : Option (Terminated 1)  -- tag 225
  datedDate : Option (Terminated 1)  -- tag 873
  text : Option (Terminated 1)  -- tag 58
  noUnderlyings : List NoUnderlyings  -- tag 711
  securityStatus : Option (Terminated 1)  -- tag 965
  noLegs : List NoLegs  -- tag 555

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 50] record.securityResponseID,
   Part.required [51, 50, 51] record.securityResponseType,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [56, 55, 51] record.datedDate,
   Part.optional [53, 56] record.text,
   Part.group [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within record.noUnderlyings,
   Part.optional [57, 54, 53] record.securityStatus,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 50]], [[51, 50, 51]], [[53, 53]], [[52, 56]], [[50, 50]], [[50, 50, 53]], [[56, 55, 51]], [[53, 56]], [55, 49, 49] :: NoUnderlyings.members, [[57, 54, 53]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseID ← readRequired [51, 50, 50] tokens
  let securityResponseType ← readRequired [51, 50, 51] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let datedDate ← readOptional [56, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  let noUnderlyings ← readGroup [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.decode tokens
  let securityStatus ← readOptional [57, 54, 53] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityResponseID, securityResponseType, symbol, securityID, securityIDSource, issueDate, datedDate, text, noUnderlyings, securityStatus, noLegs }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseID := readRequired_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityResponseType := readRequired_part [51, 50, 51] record.securityResponseType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have datedDate := readOptional_part [56, 55, 51] record.datedDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noUnderlyings := readGroup_part [55, 49, 49] [51, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within NoUnderlyings.decode NoUnderlyings.decode_encode NoUnderlyings.led record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityStatus := readOptional_part [57, 54, 53] record.securityStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityReqID, securityResponseID, securityResponseType, symbol, securityID, securityIDSource, issueDate, datedDate, text, noUnderlyings, securityStatus, noLegs, some_bind] <;> rfl

theorem SecurityDefinition.taken (record : SecurityDefinition) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 50] record.securityResponseID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50, 51] record.securityResponseType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 50, 53] record.issueDate (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [56, 55, 51] record.datedDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
           (paired_cons pairing _ _ (paired_group pairing [55, 49, 49] NoUnderlyings.members NoUnderlyings.encode NoUnderlyings.within (by decide) (by decide) NoUnderlyings.taken record.noUnderlyings)
            (paired_cons pairing _ _ (paired_optional pairing [57, 54, 53] record.securityStatus (by decide) (by decide))
             (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
              (paired_none pairing))))))))))))

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityDesc : Option (Terminated 1)  -- tag 107
  securityType : Option (Terminated 1)  -- tag 167
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  strikeCurrency : Option (Terminated 1)  -- tag 947
  currency : Option (Terminated 1)  -- tag 15
  priceQuoteCurrency : Option (Terminated 1)  -- tag 1524
  instrumentPricePrecision : Option (Terminated 1)  -- tag 2576
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  underlyingSymbol : Option (Terminated 1)  -- tag 311
  issueDate : Option (Terminated 1)  -- tag 225
  maturityDate : Option (Terminated 1)  -- tag 541
  maturityTime : Option (Terminated 1)  -- tag 1079
  minTradeVol : Option (Terminated 1)  -- tag 562
  settlType : Option (Terminated 1)  -- tag 63
  settlCurrency : Option (Terminated 1)  -- tag 120
  commCurrency : Option (Terminated 1)  -- tag 479
  contractMultiplier : Option (Terminated 1)  -- tag 231
  noSecurityAltID : Option (Terminated 1)  -- tag 454
  securityAltID : Option (Terminated 1)  -- tag 455
  securityAltIDSource : Option (Terminated 1)  -- tag 456
  noTickRules : Option (Terminated 1)  -- tag 1205
  startTickPriceRange : Option (Terminated 1)  -- tag 1206
  tickIncrement : Option (Terminated 1)  -- tag 1208
  securityStatus : Option (Terminated 1)  -- tag 965

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [57, 52, 55] record.strikeCurrency,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 53, 50, 52] record.priceQuoteCurrency,
   Part.optional [50, 53, 55, 54] record.instrumentPricePrecision,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.optional [51, 49, 49] record.underlyingSymbol,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [49, 48, 55, 57] record.maturityTime,
   Part.optional [53, 54, 50] record.minTradeVol,
   Part.optional [54, 51] record.settlType,
   Part.optional [49, 50, 48] record.settlCurrency,
   Part.optional [52, 55, 57] record.commCurrency,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [52, 53, 52] record.noSecurityAltID,
   Part.optional [52, 53, 53] record.securityAltID,
   Part.optional [52, 53, 54] record.securityAltIDSource,
   Part.optional [49, 50, 48, 53] record.noTickRules,
   Part.optional [49, 50, 48, 54] record.startTickPriceRange,
   Part.optional [49, 50, 48, 56] record.tickIncrement,
   Part.optional [57, 54, 53] record.securityStatus]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[49, 48, 55]], [[49, 54, 55]], [[50, 48, 49]], [[50, 48, 50]], [[57, 52, 55]], [[49, 53]], [[49, 53, 50, 52]], [[50, 53, 55, 54]], [[57, 54, 57]], [[51, 49, 49]], [[50, 50, 53]], [[53, 52, 49]], [[49, 48, 55, 57]], [[53, 54, 50]], [[54, 51]], [[49, 50, 48]], [[52, 55, 57]], [[50, 51, 49]], [[52, 53, 52]], [[52, 53, 53]], [[52, 53, 54]], [[49, 50, 48, 53]], [[49, 50, 48, 54]], [[49, 50, 48, 56]], [[57, 54, 53]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let strikeCurrency ← readOptional [57, 52, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let priceQuoteCurrency ← readOptional [49, 53, 50, 52] tokens
  let instrumentPricePrecision ← readOptional [50, 53, 55, 54] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let underlyingSymbol ← readOptional [51, 49, 49] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let maturityTime ← readOptional [49, 48, 55, 57] tokens
  let minTradeVol ← readOptional [53, 54, 50] tokens
  let settlType ← readOptional [54, 51] tokens
  let settlCurrency ← readOptional [49, 50, 48] tokens
  let commCurrency ← readOptional [52, 55, 57] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let noSecurityAltID ← readOptional [52, 53, 52] tokens
  let securityAltID ← readOptional [52, 53, 53] tokens
  let securityAltIDSource ← readOptional [52, 53, 54] tokens
  let noTickRules ← readOptional [49, 50, 48, 53] tokens
  let startTickPriceRange ← readOptional [49, 50, 48, 54] tokens
  let tickIncrement ← readOptional [49, 50, 48, 56] tokens
  let securityStatus ← readOptional [57, 54, 53] tokens
  pure { symbol, securityDesc, securityType, putOrCall, strikePrice, strikeCurrency, currency, priceQuoteCurrency, instrumentPricePrecision, minPriceIncrement, underlyingSymbol, issueDate, maturityDate, maturityTime, minTradeVol, settlType, settlCurrency, commCurrency, contractMultiplier, noSecurityAltID, securityAltID, securityAltIDSource, noTickRules, startTickPriceRange, tickIncrement, securityStatus }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have strikeCurrency := readOptional_part [57, 52, 55] record.strikeCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have priceQuoteCurrency := readOptional_part [49, 53, 50, 52] record.priceQuoteCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have instrumentPricePrecision := readOptional_part [50, 53, 55, 54] record.instrumentPricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have underlyingSymbol := readOptional_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityTime := readOptional_part [49, 48, 55, 57] record.maturityTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minTradeVol := readOptional_part [53, 54, 50] record.minTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have settlCurrency := readOptional_part [49, 50, 48] record.settlCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have commCurrency := readOptional_part [52, 55, 57] record.commCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noSecurityAltID := readOptional_part [52, 53, 52] record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityAltID := readOptional_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have securityAltIDSource := readOptional_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noTickRules := readOptional_part [49, 50, 48, 53] record.noTickRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have startTickPriceRange := readOptional_part [49, 50, 48, 54] record.startTickPriceRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tickIncrement := readOptional_part [49, 50, 48, 56] record.tickIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have securityStatus := readOptional_part [57, 54, 53] record.securityStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityDesc, securityType, putOrCall, strikePrice, strikeCurrency, currency, priceQuoteCurrency, instrumentPricePrecision, minPriceIncrement, underlyingSymbol, issueDate, maturityDate, maturityTime, minTradeVol, settlType, settlCurrency, commCurrency, contractMultiplier, noSecurityAltID, securityAltID, securityAltIDSource, noTickRules, startTickPriceRange, tickIncrement, securityStatus, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 52, 55] record.strikeCurrency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50, 52] record.priceQuoteCurrency (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 53, 55, 54] record.instrumentPricePrecision (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 50, 53] record.issueDate (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55, 57] record.maturityTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 54, 50] record.minTradeVol (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48] record.settlCurrency (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [52, 55, 57] record.commCurrency (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 53, 52] record.noSecurityAltID (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [52, 53, 53] record.securityAltID (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 53, 54] record.securityAltIDSource (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 53] record.noTickRules (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 54] record.startTickPriceRange (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 56] record.tickIncrement (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 54, 53] record.securityStatus (by decide) (by decide))
                            (paired_none pairing))))))))))))))))))))))))))

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure SecurityList where
  securityReqID : Terminated 1  -- tag 320
  securityResponseID : Terminated 1  -- tag 322
  securityRequestResult : Terminated 1  -- tag 560
  noRelatedSym : List NoRelatedSym  -- tag 146

def SecurityList.parts (record : SecurityList) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 50] record.securityResponseID,
   Part.required [53, 54, 48] record.securityRequestResult,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def SecurityList.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 50]], [[53, 54, 48]], [49, 52, 54] :: NoRelatedSym.members]

theorem SecurityList.shape (record : SecurityList) : record.parts.map Part.tags = SecurityList.tags := rfl

def SecurityList.decode (tokens : List Token) : Option SecurityList := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseID ← readRequired [51, 50, 50] tokens
  let securityRequestResult ← readRequired [53, 54, 48] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { securityReqID, securityResponseID, securityRequestResult, noRelatedSym }

theorem SecurityList.decode_agrees (record : SecurityList) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityList.decode tokens = some record := by
  have distinct : SecurityList.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseID := readRequired_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityRequestResult := readRequired_part [53, 54, 48] record.securityRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [SecurityList.decode, securityReqID, securityResponseID, securityRequestResult, noRelatedSym, some_bind] <;> rfl

theorem SecurityList.taken (record : SecurityList) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 50] record.securityResponseID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54, 48] record.securityRequestResult (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
      (paired_none pairing))))

structure SecurityStatus where
  securityStatusReqID : Option (Terminated 1)  -- tag 324
  symbol : Terminated 1  -- tag 55
  securityTradingStatus : Option (Terminated 1)  -- tag 326
  buyVolume : Option (Terminated 1)  -- tag 330
  sellVolume : Option (Terminated 1)  -- tag 331
  highPx : Option (Terminated 1)  -- tag 332
  lowPx : Option (Terminated 1)  -- tag 333
  lastPx : Option (Terminated 1)  -- tag 31
  text : Option (Terminated 1)  -- tag 58
  protectionRequestID : Terminated 1  -- tag 20114
  currency : Terminated 1  -- tag 15
  secondaryCurrency : Option (Terminated 1)  -- tag 5544
  protectionQtyLimit : Option (Terminated 1)  -- tag 20110
  protectionDeltaLimit : Option (Terminated 1)  -- tag 20111
  frozenLimit : Terminated 1  -- tag 20112
  intervalLength : Terminated 1  -- tag 20116
  protectionVegaLimit : Option (Terminated 1)  -- tag 20118
  maxQuoteQuantity : Option (Terminated 1)  -- tag 20119
  mMPGroup : Option (Terminated 1)  -- tag 9019

def SecurityStatus.parts (record : SecurityStatus) : List Part :=
  [Part.optional [51, 50, 52] record.securityStatusReqID,
   Part.required [53, 53] record.symbol,
   Part.optional [51, 50, 54] record.securityTradingStatus,
   Part.optional [51, 51, 48] record.buyVolume,
   Part.optional [51, 51, 49] record.sellVolume,
   Part.optional [51, 51, 50] record.highPx,
   Part.optional [51, 51, 51] record.lowPx,
   Part.optional [51, 49] record.lastPx,
   Part.optional [53, 56] record.text,
   Part.required [50, 48, 49, 49, 52] record.protectionRequestID,
   Part.required [49, 53] record.currency,
   Part.optional [53, 53, 52, 52] record.secondaryCurrency,
   Part.optional [50, 48, 49, 49, 48] record.protectionQtyLimit,
   Part.optional [50, 48, 49, 49, 49] record.protectionDeltaLimit,
   Part.required [50, 48, 49, 49, 50] record.frozenLimit,
   Part.required [50, 48, 49, 49, 54] record.intervalLength,
   Part.optional [50, 48, 49, 49, 56] record.protectionVegaLimit,
   Part.optional [50, 48, 49, 49, 57] record.maxQuoteQuantity,
   Part.optional [57, 48, 49, 57] record.mMPGroup]

def SecurityStatus.tags : List (List (List UInt8)) :=
  [[[51, 50, 52]], [[53, 53]], [[51, 50, 54]], [[51, 51, 48]], [[51, 51, 49]], [[51, 51, 50]], [[51, 51, 51]], [[51, 49]], [[53, 56]], [[50, 48, 49, 49, 52]], [[49, 53]], [[53, 53, 52, 52]], [[50, 48, 49, 49, 48]], [[50, 48, 49, 49, 49]], [[50, 48, 49, 49, 50]], [[50, 48, 49, 49, 54]], [[50, 48, 49, 49, 56]], [[50, 48, 49, 49, 57]], [[57, 48, 49, 57]]]

theorem SecurityStatus.shape (record : SecurityStatus) : record.parts.map Part.tags = SecurityStatus.tags := rfl

def SecurityStatus.decode (tokens : List Token) : Option SecurityStatus := do
  let securityStatusReqID ← readOptional [51, 50, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityTradingStatus ← readOptional [51, 50, 54] tokens
  let buyVolume ← readOptional [51, 51, 48] tokens
  let sellVolume ← readOptional [51, 51, 49] tokens
  let highPx ← readOptional [51, 51, 50] tokens
  let lowPx ← readOptional [51, 51, 51] tokens
  let lastPx ← readOptional [51, 49] tokens
  let text ← readOptional [53, 56] tokens
  let protectionRequestID ← readRequired [50, 48, 49, 49, 52] tokens
  let currency ← readRequired [49, 53] tokens
  let secondaryCurrency ← readOptional [53, 53, 52, 52] tokens
  let protectionQtyLimit ← readOptional [50, 48, 49, 49, 48] tokens
  let protectionDeltaLimit ← readOptional [50, 48, 49, 49, 49] tokens
  let frozenLimit ← readRequired [50, 48, 49, 49, 50] tokens
  let intervalLength ← readRequired [50, 48, 49, 49, 54] tokens
  let protectionVegaLimit ← readOptional [50, 48, 49, 49, 56] tokens
  let maxQuoteQuantity ← readOptional [50, 48, 49, 49, 57] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  pure { securityStatusReqID, symbol, securityTradingStatus, buyVolume, sellVolume, highPx, lowPx, lastPx, text, protectionRequestID, currency, secondaryCurrency, protectionQtyLimit, protectionDeltaLimit, frozenLimit, intervalLength, protectionVegaLimit, maxQuoteQuantity, mMPGroup }

theorem SecurityStatus.decode_agrees (record : SecurityStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityStatus.decode tokens = some record := by
  have distinct : SecurityStatus.tags.flatten.Nodup := by decide +kernel
  have securityStatusReqID := readOptional_part [51, 50, 52] record.securityStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityTradingStatus := readOptional_part [51, 50, 54] record.securityTradingStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have buyVolume := readOptional_part [51, 51, 48] record.buyVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sellVolume := readOptional_part [51, 51, 49] record.sellVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have highPx := readOptional_part [51, 51, 50] record.highPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lowPx := readOptional_part [51, 51, 51] record.lowPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have protectionRequestID := readRequired_part [50, 48, 49, 49, 52] record.protectionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have secondaryCurrency := readOptional_part [53, 53, 52, 52] record.secondaryCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have protectionQtyLimit := readOptional_part [50, 48, 49, 49, 48] record.protectionQtyLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have protectionDeltaLimit := readOptional_part [50, 48, 49, 49, 49] record.protectionDeltaLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have frozenLimit := readRequired_part [50, 48, 49, 49, 50] record.frozenLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have intervalLength := readRequired_part [50, 48, 49, 49, 54] record.intervalLength tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have protectionVegaLimit := readOptional_part [50, 48, 49, 49, 56] record.protectionVegaLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maxQuoteQuantity := readOptional_part [50, 48, 49, 49, 57] record.maxQuoteQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [SecurityStatus.decode, securityStatusReqID, symbol, securityTradingStatus, buyVolume, sellVolume, highPx, lowPx, lastPx, text, protectionRequestID, currency, secondaryCurrency, protectionQtyLimit, protectionDeltaLimit, frozenLimit, intervalLength, protectionVegaLimit, maxQuoteQuantity, mMPGroup, some_bind] <;> rfl

theorem SecurityStatus.taken (record : SecurityStatus) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 50, 52] record.securityStatusReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 50, 54] record.securityTradingStatus (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 51, 48] record.buyVolume (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 51, 49] record.sellVolume (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 51, 50] record.highPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 51, 51] record.lowPx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 52] record.protectionRequestID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52, 52] record.secondaryCurrency (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 48] record.protectionQtyLimit (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 49] record.protectionDeltaLimit (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 50] record.frozenLimit (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 54] record.intervalLength (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 56] record.protectionVegaLimit (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 57] record.maxQuoteQuantity (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

structure SequenceReset where
  newSeqNo : Terminated 1  -- tag 36

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [51, 54] record.newSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[51, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let newSeqNo ← readRequired [51, 54] tokens
  pure { newSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [SequenceReset.decode, newSeqNo, some_bind] <;> rfl

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
   (paired_none pairing)

structure TestRequest where
  testReqId : Terminated 1  -- tag 112

def TestRequest.parts (record : TestRequest) : List Part :=
  [Part.required [49, 49, 50] record.testReqId]

def TestRequest.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem TestRequest.shape (record : TestRequest) : record.parts.map Part.tags = TestRequest.tags := rfl

def TestRequest.decode (tokens : List Token) : Option TestRequest := do
  let testReqId ← readRequired [49, 49, 50] tokens
  pure { testReqId }

theorem TestRequest.decode_agrees (record : TestRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TestRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TestRequest.decode tokens = some record := by
  have distinct : TestRequest.tags.flatten.Nodup := by decide +kernel
  have testReqId := readRequired_part [49, 49, 50] record.testReqId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [TestRequest.decode, testReqId, some_bind] <;> rfl

theorem TestRequest.taken (record : TestRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqId (by decide) (by decide))
   (paired_none pairing)

structure TradeCaptureReportRequestAck where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  tradeRequestResult : Terminated 1  -- tag 571
  tradeRequestStatus : Terminated 1  -- tag 750
  symbol : Terminated 1  -- tag 55

def TradeCaptureReportRequestAck.parts (record : TradeCaptureReportRequestAck) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.required [53, 55, 49] record.tradeRequestResult,
   Part.required [55, 53, 48] record.tradeRequestStatus,
   Part.required [53, 53] record.symbol]

def TradeCaptureReportRequestAck.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[53, 55, 49]], [[55, 53, 48]], [[53, 53]]]

theorem TradeCaptureReportRequestAck.shape (record : TradeCaptureReportRequestAck) : record.parts.map Part.tags = TradeCaptureReportRequestAck.tags := rfl

def TradeCaptureReportRequestAck.decode (tokens : List Token) : Option TradeCaptureReportRequestAck := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let tradeRequestResult ← readRequired [53, 55, 49] tokens
  let tradeRequestStatus ← readRequired [55, 53, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  pure { tradeRequestID, tradeRequestType, tradeRequestResult, tradeRequestStatus, symbol }

theorem TradeCaptureReportRequestAck.decode_agrees (record : TradeCaptureReportRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequestAck.decode tokens = some record := by
  have distinct : TradeCaptureReportRequestAck.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradeRequestResult := readRequired_part [53, 55, 49] record.tradeRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeRequestStatus := readRequired_part [55, 53, 48] record.tradeRequestStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [TradeCaptureReportRequestAck.decode, tradeRequestID, tradeRequestType, tradeRequestResult, tradeRequestStatus, symbol, some_bind] <;> rfl

theorem TradeCaptureReportRequestAck.taken (record : TradeCaptureReportRequestAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54, 57] record.tradeRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 55, 49] record.tradeRequestResult (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [55, 53, 48] record.tradeRequestStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_none pairing)))))

structure TradeCaptureReport where
  tradeRequestID : Option (Terminated 1)  -- tag 568
  previouslyReported : Terminated 1  -- tag 570
  symbol : Terminated 1  -- tag 55
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  tradeId : Terminated 1  -- tag 1003
  secondaryTradeId : Option (Terminated 1)  -- tag 1040
  tradeDate : Terminated 1  -- tag 75
  transactTime : Terminated 1  -- tag 60
  noLegs : Option (Terminated 1)  -- tag 555
  legSymbol : Option (Terminated 1)  -- tag 600
  legQty : Terminated 1  -- tag 687
  legPrice : Terminated 1  -- tag 566
  legSide : Terminated 1  -- tag 624
  noSides : Terminated 1  -- tag 552
  side : Terminated 1  -- tag 54
  orderId : Terminated 1  -- tag 37
  commission : Terminated 1  -- tag 12
  commCurrency : Terminated 1  -- tag 479

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.optional [53, 54, 56] record.tradeRequestID,
   Part.required [53, 55, 48] record.previouslyReported,
   Part.required [53, 53] record.symbol,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.required [49, 48, 48, 51] record.tradeId,
   Part.optional [49, 48, 52, 48] record.secondaryTradeId,
   Part.required [55, 53] record.tradeDate,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 53, 53] record.noLegs,
   Part.optional [54, 48, 48] record.legSymbol,
   Part.required [54, 56, 55] record.legQty,
   Part.required [53, 54, 54] record.legPrice,
   Part.required [54, 50, 52] record.legSide,
   Part.required [53, 53, 50] record.noSides,
   Part.required [53, 52] record.side,
   Part.required [51, 55] record.orderId,
   Part.required [49, 50] record.commission,
   Part.required [52, 55, 57] record.commCurrency]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 55, 48]], [[53, 53]], [[51, 50]], [[51, 49]], [[49, 48, 48, 51]], [[49, 48, 52, 48]], [[55, 53]], [[54, 48]], [[53, 53, 53]], [[54, 48, 48]], [[54, 56, 55]], [[53, 54, 54]], [[54, 50, 52]], [[53, 53, 50]], [[53, 52]], [[51, 55]], [[49, 50]], [[52, 55, 57]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeRequestID ← readOptional [53, 54, 56] tokens
  let previouslyReported ← readRequired [53, 55, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let tradeId ← readRequired [49, 48, 48, 51] tokens
  let secondaryTradeId ← readOptional [49, 48, 52, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let noLegs ← readOptional [53, 53, 53] tokens
  let legSymbol ← readOptional [54, 48, 48] tokens
  let legQty ← readRequired [54, 56, 55] tokens
  let legPrice ← readRequired [53, 54, 54] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let noSides ← readRequired [53, 53, 50] tokens
  let side ← readRequired [53, 52] tokens
  let orderId ← readRequired [51, 55] tokens
  let commission ← readRequired [49, 50] tokens
  let commCurrency ← readRequired [52, 55, 57] tokens
  pure { tradeRequestID, previouslyReported, symbol, lastQty, lastPx, tradeId, secondaryTradeId, tradeDate, transactTime, noLegs, legSymbol, legQty, legPrice, legSide, noSides, side, orderId, commission, commCurrency }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readOptional_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have previouslyReported := readRequired_part [53, 55, 48] record.previouslyReported tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeId := readRequired_part [49, 48, 48, 51] record.tradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have secondaryTradeId := readOptional_part [49, 48, 52, 48] record.secondaryTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noLegs := readOptional_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have legSymbol := readOptional_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have legQty := readRequired_part [54, 56, 55] record.legQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have legPrice := readRequired_part [53, 54, 54] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noSides := readRequired_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderId := readRequired_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have commission := readRequired_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have commCurrency := readRequired_part [52, 55, 57] record.commCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeRequestID, previouslyReported, symbol, lastQty, lastPx, tradeId, secondaryTradeId, tradeDate, transactTime, noLegs, legSymbol, legQty, legPrice, legSide, noSides, side, orderId, commission, commCurrency, some_bind] <;> rfl

theorem TradeCaptureReport.taken (record : TradeCaptureReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 55, 48] record.previouslyReported (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 51] record.tradeId (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 52, 48] record.secondaryTradeId (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 53, 53] record.noLegs (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [54, 56, 55] record.legQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [53, 54, 54] record.legPrice (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [54, 50, 52] record.legSide (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [53, 53, 50] record.noSides (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderId (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [49, 50] record.commission (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [52, 55, 57] record.commCurrency (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

structure UserResponse where
  userRequestID : Terminated 1  -- tag 923
  username : Terminated 1  -- tag 553
  userStatus : Option (Terminated 1)  -- tag 926
  currency : Option (Terminated 1)  -- tag 15
  deribitUserEquity : Option (Terminated 1)  -- tag 100001
  deribitUserBalance : Option (Terminated 1)  -- tag 100002
  deribitUserInitialMargin : Option (Terminated 1)  -- tag 100003
  deribitUserMaintenanceMargin : Option (Terminated 1)  -- tag 100004
  deribitUnrealizedPl : Option (Terminated 1)  -- tag 100005
  deribitRealizedPl : Option (Terminated 1)  -- tag 100006
  deribitTotalPl : Option (Terminated 1)  -- tag 100011
  deribitMarginBalance : Option (Terminated 1)  -- tag 100013

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [53, 53, 51] record.username,
   Part.optional [57, 50, 54] record.userStatus,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 48, 48, 48, 48, 49] record.deribitUserEquity,
   Part.optional [49, 48, 48, 48, 48, 50] record.deribitUserBalance,
   Part.optional [49, 48, 48, 48, 48, 51] record.deribitUserInitialMargin,
   Part.optional [49, 48, 48, 48, 48, 52] record.deribitUserMaintenanceMargin,
   Part.optional [49, 48, 48, 48, 48, 53] record.deribitUnrealizedPl,
   Part.optional [49, 48, 48, 48, 48, 54] record.deribitRealizedPl,
   Part.optional [49, 48, 48, 48, 49, 49] record.deribitTotalPl,
   Part.optional [49, 48, 48, 48, 49, 51] record.deribitMarginBalance]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[53, 53, 51]], [[57, 50, 54]], [[49, 53]], [[49, 48, 48, 48, 48, 49]], [[49, 48, 48, 48, 48, 50]], [[49, 48, 48, 48, 48, 51]], [[49, 48, 48, 48, 48, 52]], [[49, 48, 48, 48, 48, 53]], [[49, 48, 48, 48, 48, 54]], [[49, 48, 48, 48, 49, 49]], [[49, 48, 48, 48, 49, 51]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let username ← readRequired [53, 53, 51] tokens
  let userStatus ← readOptional [57, 50, 54] tokens
  let currency ← readOptional [49, 53] tokens
  let deribitUserEquity ← readOptional [49, 48, 48, 48, 48, 49] tokens
  let deribitUserBalance ← readOptional [49, 48, 48, 48, 48, 50] tokens
  let deribitUserInitialMargin ← readOptional [49, 48, 48, 48, 48, 51] tokens
  let deribitUserMaintenanceMargin ← readOptional [49, 48, 48, 48, 48, 52] tokens
  let deribitUnrealizedPl ← readOptional [49, 48, 48, 48, 48, 53] tokens
  let deribitRealizedPl ← readOptional [49, 48, 48, 48, 48, 54] tokens
  let deribitTotalPl ← readOptional [49, 48, 48, 48, 49, 49] tokens
  let deribitMarginBalance ← readOptional [49, 48, 48, 48, 49, 51] tokens
  pure { userRequestID, username, userStatus, currency, deribitUserEquity, deribitUserBalance, deribitUserInitialMargin, deribitUserMaintenanceMargin, deribitUnrealizedPl, deribitRealizedPl, deribitTotalPl, deribitMarginBalance }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userStatus := readOptional_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have deribitUserEquity := readOptional_part [49, 48, 48, 48, 48, 49] record.deribitUserEquity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deribitUserBalance := readOptional_part [49, 48, 48, 48, 48, 50] record.deribitUserBalance tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deribitUserInitialMargin := readOptional_part [49, 48, 48, 48, 48, 51] record.deribitUserInitialMargin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deribitUserMaintenanceMargin := readOptional_part [49, 48, 48, 48, 48, 52] record.deribitUserMaintenanceMargin tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have deribitUnrealizedPl := readOptional_part [49, 48, 48, 48, 48, 53] record.deribitUnrealizedPl tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have deribitRealizedPl := readOptional_part [49, 48, 48, 48, 48, 54] record.deribitRealizedPl tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deribitTotalPl := readOptional_part [49, 48, 48, 48, 49, 49] record.deribitTotalPl tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deribitMarginBalance := readOptional_part [49, 48, 48, 48, 49, 51] record.deribitMarginBalance tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [UserResponse.decode, userRequestID, username, userStatus, currency, deribitUserEquity, deribitUserBalance, deribitUserInitialMargin, deribitUserMaintenanceMargin, deribitUnrealizedPl, deribitRealizedPl, deribitTotalPl, deribitMarginBalance, some_bind] <;> rfl

theorem UserResponse.taken (record : UserResponse) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 50, 51] record.userRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [57, 50, 54] record.userStatus (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 49] record.deribitUserEquity (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 50] record.deribitUserBalance (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 51] record.deribitUserInitialMargin (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 52] record.deribitUserMaintenanceMargin (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 53] record.deribitUnrealizedPl (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 54] record.deribitRealizedPl (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 49] record.deribitTotalPl (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 51] record.deribitMarginBalance (by decide) (by decide))
              (paired_none pairing))))))))))))

inductive Message where
  | executionReport (header : Header) (r0 : ExecutionReport)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh)
  | marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject)
  | marketDataSnapshot (header : Header) (r0 : MarketDataSnapshot)
  | massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement)
  | mMProtectionLimitsResult (header : Header) (r0 : MMProtectionLimitsResult)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)
  | orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport)
  | positionReport (header : Header) (r0 : PositionReport)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | securityList (header : Header) (r0 : SecurityList)
  | securityStatus (header : Header) (r0 : SecurityStatus)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | userResponse (header : Header) (r0 : UserResponse)

def Message.tokens : Message → List Token
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataIncrementalRefresh header r0 => ⟨[51, 53], [88]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequestReject header r0 => ⟨[51, 53], [89]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataSnapshot header r0 => ⟨[51, 53], [87]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuoteAcknowledgement header r0 => ⟨[51, 53], [98]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .mMProtectionLimitsResult header r0 => ⟨[51, 53], [77, 82]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelReport header r0 => ⟨[51, 53], [114]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .positionReport header r0 => ⟨[51, 53], [65, 80]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], [100]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityList header r0 => ⟨[51, 53], [121]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityStatus header r0 => ⟨[51, 53], [102]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequestAck header r0 => ⟨[51, 53], [65, 81]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], [65, 69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], [66, 70]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value = [88] then
        if known (Header.tags ++ MarketDataIncrementalRefresh.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataIncrementalRefresh.decode rest
          pure (.marketDataIncrementalRefresh header r0)
        else none
      else if token.value = [89] then
        if known (Header.tags ++ MarketDataRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequestReject.decode rest
          pure (.marketDataRequestReject header r0)
        else none
      else if token.value = [87] then
        if known (Header.tags ++ MarketDataSnapshot.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataSnapshot.decode rest
          pure (.marketDataSnapshot header r0)
        else none
      else if token.value = [98] then
        if known (Header.tags ++ MassQuoteAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuoteAcknowledgement.decode rest
          pure (.massQuoteAcknowledgement header r0)
        else none
      else if token.value = [77, 82] then
        if known (Header.tags ++ MMProtectionLimitsResult.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MMProtectionLimitsResult.decode rest
          pure (.mMProtectionLimitsResult header r0)
        else none
      else if token.value = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else if token.value = [114] then
        if known (Header.tags ++ OrderMassCancelReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelReport.decode rest
          pure (.orderMassCancelReport header r0)
        else none
      else if token.value = [65, 80] then
        if known (Header.tags ++ PositionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PositionReport.decode rest
          pure (.positionReport header r0)
        else none
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value = [121] then
        if known (Header.tags ++ SecurityList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityList.decode rest
          pure (.securityList header r0)
        else none
      else if token.value = [102] then
        if known (Header.tags ++ SecurityStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityStatus.decode rest
          pure (.securityStatus header r0)
        else none
      else if token.value = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value = [65, 81] then
        if known (Header.tags ++ TradeCaptureReportRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequestAck.decode rest
          pure (.tradeCaptureReportRequestAck header r0)
        else none
      else if token.value = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else none
    else none

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

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

theorem Message.decode_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decode (Message.tokens (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataIncrementalRefresh.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataIncrementalRefresh.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject) :
    Message.decode (Message.tokens (.marketDataRequestReject header r0)) = some (.marketDataRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataSnapshot (header : Header) (r0 : MarketDataSnapshot) :
    Message.decode (Message.tokens (.marketDataSnapshot header r0)) = some (.marketDataSnapshot header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshot.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataSnapshot.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshot.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataSnapshot.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decode (Message.tokens (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuoteAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuoteAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuoteAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_mMProtectionLimitsResult (header : Header) (r0 : MMProtectionLimitsResult) :
    Message.decode (Message.tokens (.mMProtectionLimitsResult header r0)) = some (.mMProtectionLimitsResult header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionLimitsResult.tags) rfl rfl (by decide +kernel))
  have c1 := MMProtectionLimitsResult.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionLimitsResult.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MMProtectionLimitsResult.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decode (Message.tokens (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_positionReport (header : Header) (r0 : PositionReport) :
    Message.decode (Message.tokens (.positionReport header r0)) = some (.positionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PositionReport.tags) rfl rfl (by decide +kernel))
  have c1 := PositionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PositionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PositionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityList (header : Header) (r0 : SecurityList) :
    Message.decode (Message.tokens (.securityList header r0)) = some (.securityList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityStatus (header : Header) (r0 : SecurityStatus) :
    Message.decode (Message.tokens (.securityStatus header r0)) = some (.securityStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatus.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityStatus.tags) rfl
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

theorem Message.decode_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decode (Message.tokens (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decode_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decode_marketDataRequestReject header r0
  | marketDataSnapshot header r0 => exact Message.decode_marketDataSnapshot header r0
  | massQuoteAcknowledgement header r0 => exact Message.decode_massQuoteAcknowledgement header r0
  | mMProtectionLimitsResult header r0 => exact Message.decode_mMProtectionLimitsResult header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0
  | orderMassCancelReport header r0 => exact Message.decode_orderMassCancelReport header r0
  | positionReport header r0 => exact Message.decode_positionReport header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | securityList header r0 => exact Message.decode_securityList header r0
  | securityStatus header r0 => exact Message.decode_securityStatus header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decode_tradeCaptureReportRequestAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ExecutionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logout.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decodeBytes (Message.encode (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [88]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataIncrementalRefresh.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataIncrementalRefresh header r0

theorem Message.decodeBytes_marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject) :
    Message.decodeBytes (Message.encode (.marketDataRequestReject header r0)) = some (.marketDataRequestReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [89]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataRequestReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequestReject header r0

theorem Message.decodeBytes_marketDataSnapshot (header : Header) (r0 : MarketDataSnapshot) :
    Message.decodeBytes (Message.encode (.marketDataSnapshot header r0)) = some (.marketDataSnapshot header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [87]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataSnapshot.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataSnapshot header r0

theorem Message.decodeBytes_massQuoteAcknowledgement (header : Header) (r0 : MassQuoteAcknowledgement) :
    Message.decodeBytes (Message.encode (.massQuoteAcknowledgement header r0)) = some (.massQuoteAcknowledgement header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [98]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MassQuoteAcknowledgement.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuoteAcknowledgement header r0

theorem Message.decodeBytes_mMProtectionLimitsResult (header : Header) (r0 : MMProtectionLimitsResult) :
    Message.decodeBytes (Message.encode (.mMProtectionLimitsResult header r0)) = some (.mMProtectionLimitsResult header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [77, 82]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MMProtectionLimitsResult.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_mMProtectionLimitsResult header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_orderMassCancelReport (header : Header) (r0 : OrderMassCancelReport) :
    Message.decodeBytes (Message.encode (.orderMassCancelReport header r0)) = some (.orderMassCancelReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [114]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderMassCancelReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelReport header r0

theorem Message.decodeBytes_positionReport (header : Header) (r0 : PositionReport) :
    Message.decodeBytes (Message.encode (.positionReport header r0)) = some (.positionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 80]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (PositionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_positionReport header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [50]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ResendRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [100]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinition.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_securityList (header : Header) (r0 : SecurityList) :
    Message.decodeBytes (Message.encode (.securityList header r0)) = some (.securityList header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [121]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityList.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityList header r0

theorem Message.decodeBytes_securityStatus (header : Header) (r0 : SecurityStatus) :
    Message.decodeBytes (Message.encode (.securityStatus header r0)) = some (.securityStatus header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [102]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityStatus.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityStatus header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [49]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TestRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 81]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReportRequestAck.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequestAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66, 70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserResponse.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decodeBytes_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decodeBytes_marketDataRequestReject header r0
  | marketDataSnapshot header r0 => exact Message.decodeBytes_marketDataSnapshot header r0
  | massQuoteAcknowledgement header r0 => exact Message.decodeBytes_massQuoteAcknowledgement header r0
  | mMProtectionLimitsResult header r0 => exact Message.decodeBytes_mMProtectionLimitsResult header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0
  | orderMassCancelReport header r0 => exact Message.decodeBytes_orderMassCancelReport header r0
  | positionReport header r0 => exact Message.decodeBytes_positionReport header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | securityList header r0 => exact Message.decodeBytes_securityList header r0
  | securityStatus header r0 => exact Message.decodeBytes_securityStatus header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decodeBytes_tradeCaptureReportRequestAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseDeribitOrderentryFixV10Exchange
