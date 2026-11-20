import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v1.0.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNtxequitiesCoredropcopyFixV1002026Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  possDupFlag : Option (Terminated 1)  -- tag 43
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[52, 51]], [[51, 52]], [[53, 50]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, possDupFlag, msgSeqNum, sendingTime, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, possDupFlag, msgSeqNum, sendingTime, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
        (paired_none pairing))))))

structure ExecutionReport where
  deliverToCompID : Option (Terminated 1)  -- tag 128
  targetSubID : Terminated 1  -- tag 57
  senderSubID : Option (Terminated 1)  -- tag 50
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  ordStatus : Terminated 1  -- tag 39
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  leavesQty : Option (Terminated 1)  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  price : Option (Terminated 1)  -- tag 44
  ordType : Option (Terminated 1)  -- tag 40
  execBroker : Option (Terminated 1)  -- tag 76
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Option (Terminated 1)  -- tag 59
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49, 50, 56] record.deliverToCompID,
   Part.required [53, 55] record.targetSubID,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.optional [52, 52] record.price,
   Part.optional [52, 48] record.ordType,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49, 50, 56]], [[53, 55]], [[53, 48]], [[49]], [[49, 49]], [[49, 55]], [[50, 48]], [[51, 57]], [[53, 53]], [[53, 52]], [[51, 56]], [[49, 53, 49]], [[49, 52]], [[54]], [[52, 52]], [[52, 48]], [[55, 54]], [[49, 56]], [[53, 57]], [[53, 56]], [[54, 48]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let price ← readOptional [52, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  pure { deliverToCompID, targetSubID, senderSubID, account, clOrdID, execID, execTransType, ordStatus, symbol, side, orderQty, leavesQty, cumQty, avgPx, price, ordType, execBroker, execInst, timeInForce, text, transactTime }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [ExecutionReport.decode, deliverToCompID, targetSubID, senderSubID, account, clOrdID, execID, execTransType, ordStatus, symbol, side, orderQty, leavesQty, cumQty, avgPx, price, ordType, execBroker, execInst, timeInForce, text, transactTime, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                       (paired_none pairing)))))))))))))))))))))

structure ExecutionReportOrderAcknowledgement where
  orderID : Terminated 1  -- tag 37
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  maxFloor : Option (Terminated 1)  -- tag 111
  userRefNum : Option (Terminated 1)  -- tag 20001
  displayInstruction : Option (Terminated 1)  -- tag 9140
  crossType : Option (Terminated 1)  -- tag 9355
  minQty : Option (Terminated 1)  -- tag 110
  pegOffset : Option (Terminated 1)  -- tag 211
  discretionPrice : Option (Terminated 1)  -- tag 20009
  discretionPriceType : Option (Terminated 1)  -- tag 388
  discretionPegOffset : Option (Terminated 1)  -- tag 389
  randomReserves : Option (Terminated 1)  -- tag 8020
  expireTime : Option (Terminated 1)  -- tag 126
  handleInst : Option (Terminated 1)  -- tag 20003
  groupID : Option (Terminated 1)  -- tag 20107
  bBOWeightIndicator : Option (Terminated 1)  -- tag 9883
  locateBroker : Option (Terminated 1)  -- tag 21002

def ExecutionReportOrderAcknowledgement.parts (record : ExecutionReportOrderAcknowledgement) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 48, 48, 48, 49] record.userRefNum,
   Part.optional [57, 49, 52, 48] record.displayInstruction,
   Part.optional [57, 51, 53, 53] record.crossType,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegOffset,
   Part.optional [50, 48, 48, 48, 57] record.discretionPrice,
   Part.optional [51, 56, 56] record.discretionPriceType,
   Part.optional [51, 56, 57] record.discretionPegOffset,
   Part.optional [56, 48, 50, 48] record.randomReserves,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 48, 48, 51] record.handleInst,
   Part.optional [50, 48, 49, 48, 55] record.groupID,
   Part.optional [57, 56, 56, 51] record.bBOWeightIndicator,
   Part.optional [50, 49, 48, 48, 50] record.locateBroker]

def ExecutionReportOrderAcknowledgement.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[51, 50]], [[51, 49]], [[52, 55]], [[50, 57]], [[49, 49, 49]], [[50, 48, 48, 48, 49]], [[57, 49, 52, 48]], [[57, 51, 53, 53]], [[49, 49, 48]], [[50, 49, 49]], [[50, 48, 48, 48, 57]], [[51, 56, 56]], [[51, 56, 57]], [[56, 48, 50, 48]], [[49, 50, 54]], [[50, 48, 48, 48, 51]], [[50, 48, 49, 48, 55]], [[57, 56, 56, 51]], [[50, 49, 48, 48, 50]]]

theorem ExecutionReportOrderAcknowledgement.shape (record : ExecutionReportOrderAcknowledgement) : record.parts.map Part.tags = ExecutionReportOrderAcknowledgement.tags := rfl

def ExecutionReportOrderAcknowledgement.decode (tokens : List Token) : Option ExecutionReportOrderAcknowledgement := do
  let orderID ← readRequired [51, 55] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let userRefNum ← readOptional [50, 48, 48, 48, 49] tokens
  let displayInstruction ← readOptional [57, 49, 52, 48] tokens
  let crossType ← readOptional [57, 51, 53, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegOffset ← readOptional [50, 49, 49] tokens
  let discretionPrice ← readOptional [50, 48, 48, 48, 57] tokens
  let discretionPriceType ← readOptional [51, 56, 56] tokens
  let discretionPegOffset ← readOptional [51, 56, 57] tokens
  let randomReserves ← readOptional [56, 48, 50, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let handleInst ← readOptional [50, 48, 48, 48, 51] tokens
  let groupID ← readOptional [50, 48, 49, 48, 55] tokens
  let bBOWeightIndicator ← readOptional [57, 56, 56, 51] tokens
  let locateBroker ← readOptional [50, 49, 48, 48, 50] tokens
  pure { orderID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, userRefNum, displayInstruction, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, bBOWeightIndicator, locateBroker }

theorem ExecutionReportOrderAcknowledgement.decode_agrees (record : ExecutionReportOrderAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportOrderAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOrderAcknowledgement.decode tokens = some record := by
  have distinct : ExecutionReportOrderAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have userRefNum := readOptional_part [50, 48, 48, 48, 49] record.userRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have displayInstruction := readOptional_part [57, 49, 52, 48] record.displayInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have crossType := readOptional_part [57, 51, 53, 53] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffset := readOptional_part [50, 49, 49] record.pegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have discretionPrice := readOptional_part [50, 48, 48, 48, 57] record.discretionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have discretionPriceType := readOptional_part [51, 56, 56] record.discretionPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have discretionPegOffset := readOptional_part [51, 56, 57] record.discretionPegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have randomReserves := readOptional_part [56, 48, 50, 48] record.randomReserves tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have handleInst := readOptional_part [50, 48, 48, 48, 51] record.handleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have groupID := readOptional_part [50, 48, 49, 48, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have bBOWeightIndicator := readOptional_part [57, 56, 56, 51] record.bBOWeightIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have locateBroker := readOptional_part [50, 49, 48, 48, 50] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [ExecutionReportOrderAcknowledgement.decode, orderID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, userRefNum, displayInstruction, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, bBOWeightIndicator, locateBroker, some_bind] <;> rfl

theorem ExecutionReportOrderAcknowledgement.taken (record : ExecutionReportOrderAcknowledgement) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.userRefNum (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 49, 52, 48] record.displayInstruction (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffset (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 57] record.discretionPrice (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionPriceType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionPegOffset (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.randomReserves (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.handleInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 48, 55] record.groupID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 51] record.bBOWeightIndicator (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48, 48, 50] record.locateBroker (by decide) (by decide))
                      (paired_none pairing))))))))))))))))))))

structure ExecutionReportPartialFill where
  orderID : Terminated 1  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  maxFloor : Option (Terminated 1)  -- tag 111
  tradeDate : Option (Terminated 1)  -- tag 75
  liquidityFlag : Option (Terminated 1)  -- tag 9882
  lastExchange : Option (Terminated 1)  -- tag 30
  userRefNum : Option (Terminated 1)  -- tag 20001
  crossType : Option (Terminated 1)  -- tag 9355
  minQty : Option (Terminated 1)  -- tag 110
  pegOffset : Option (Terminated 1)  -- tag 211
  discretionPrice : Option (Terminated 1)  -- tag 20009
  discretionPriceType : Option (Terminated 1)  -- tag 388
  discretionPegOffset : Option (Terminated 1)  -- tag 389
  randomReserves : Option (Terminated 1)  -- tag 8020
  expireTime : Option (Terminated 1)  -- tag 126
  handleInst : Option (Terminated 1)  -- tag 20003
  groupID : Option (Terminated 1)  -- tag 20107
  locateBroker : Option (Terminated 1)  -- tag 21002

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [57, 56, 56, 50] record.liquidityFlag,
   Part.optional [51, 48] record.lastExchange,
   Part.optional [50, 48, 48, 48, 49] record.userRefNum,
   Part.optional [57, 51, 53, 53] record.crossType,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegOffset,
   Part.optional [50, 48, 48, 48, 57] record.discretionPrice,
   Part.optional [51, 56, 56] record.discretionPriceType,
   Part.optional [51, 56, 57] record.discretionPegOffset,
   Part.optional [56, 48, 50, 48] record.randomReserves,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 48, 48, 51] record.handleInst,
   Part.optional [50, 48, 49, 48, 55] record.groupID,
   Part.optional [50, 49, 48, 48, 50] record.locateBroker]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 48, 57]], [[51, 50]], [[51, 49]], [[52, 55]], [[50, 57]], [[49, 49, 49]], [[55, 53]], [[57, 56, 56, 50]], [[51, 48]], [[50, 48, 48, 48, 49]], [[57, 51, 53, 53]], [[49, 49, 48]], [[50, 49, 49]], [[50, 48, 48, 48, 57]], [[51, 56, 56]], [[51, 56, 57]], [[56, 48, 50, 48]], [[49, 50, 54]], [[50, 48, 48, 48, 51]], [[50, 48, 49, 48, 55]], [[50, 49, 48, 48, 50]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let orderID ← readRequired [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let liquidityFlag ← readOptional [57, 56, 56, 50] tokens
  let lastExchange ← readOptional [51, 48] tokens
  let userRefNum ← readOptional [50, 48, 48, 48, 49] tokens
  let crossType ← readOptional [57, 51, 53, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegOffset ← readOptional [50, 49, 49] tokens
  let discretionPrice ← readOptional [50, 48, 48, 48, 57] tokens
  let discretionPriceType ← readOptional [51, 56, 56] tokens
  let discretionPegOffset ← readOptional [51, 56, 57] tokens
  let randomReserves ← readOptional [56, 48, 50, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let handleInst ← readOptional [50, 48, 48, 48, 51] tokens
  let groupID ← readOptional [50, 48, 49, 48, 55] tokens
  let locateBroker ← readOptional [50, 49, 48, 48, 50] tokens
  pure { orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, tradeDate, liquidityFlag, lastExchange, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have liquidityFlag := readOptional_part [57, 56, 56, 50] record.liquidityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastExchange := readOptional_part [51, 48] record.lastExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have userRefNum := readOptional_part [50, 48, 48, 48, 49] record.userRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have crossType := readOptional_part [57, 51, 53, 53] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have pegOffset := readOptional_part [50, 49, 49] record.pegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have discretionPrice := readOptional_part [50, 48, 48, 48, 57] record.discretionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have discretionPriceType := readOptional_part [51, 56, 56] record.discretionPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have discretionPegOffset := readOptional_part [51, 56, 57] record.discretionPegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have randomReserves := readOptional_part [56, 48, 50, 48] record.randomReserves tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have handleInst := readOptional_part [50, 48, 48, 48, 51] record.handleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have groupID := readOptional_part [50, 48, 49, 48, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have locateBroker := readOptional_part [50, 49, 48, 48, 50] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, tradeDate, liquidityFlag, lastExchange, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker, some_bind] <;> rfl

theorem ExecutionReportPartialFill.taken (record : ExecutionReportPartialFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.liquidityFlag (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastExchange (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.userRefNum (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffset (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 57] record.discretionPrice (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionPriceType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionPegOffset (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.randomReserves (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.handleInst (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 48, 55] record.groupID (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48, 48, 50] record.locateBroker (by decide) (by decide))
                        (paired_none pairing))))))))))))))))))))))

structure ExecutionReportFilledOrBrokenTrade where
  orderID : Terminated 1  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  maxFloor : Option (Terminated 1)  -- tag 111
  execRefID : Option (Terminated 1)  -- tag 19
  tradeDate : Option (Terminated 1)  -- tag 75
  liquidityFlag : Option (Terminated 1)  -- tag 9882
  lastExchange : Option (Terminated 1)  -- tag 30
  userRefNum : Option (Terminated 1)  -- tag 20001
  crossType : Option (Terminated 1)  -- tag 9355
  minQty : Option (Terminated 1)  -- tag 110
  pegOffset : Option (Terminated 1)  -- tag 211
  discretionPrice : Option (Terminated 1)  -- tag 20009
  discretionPriceType : Option (Terminated 1)  -- tag 388
  discretionPegOffset : Option (Terminated 1)  -- tag 389
  randomReserves : Option (Terminated 1)  -- tag 8020
  expireTime : Option (Terminated 1)  -- tag 126
  handleInst : Option (Terminated 1)  -- tag 20003
  groupID : Option (Terminated 1)  -- tag 20107
  locateBroker : Option (Terminated 1)  -- tag 21002

def ExecutionReportFilledOrBrokenTrade.parts (record : ExecutionReportFilledOrBrokenTrade) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 57] record.execRefID,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [57, 56, 56, 50] record.liquidityFlag,
   Part.optional [51, 48] record.lastExchange,
   Part.optional [50, 48, 48, 48, 49] record.userRefNum,
   Part.optional [57, 51, 53, 53] record.crossType,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegOffset,
   Part.optional [50, 48, 48, 48, 57] record.discretionPrice,
   Part.optional [51, 56, 56] record.discretionPriceType,
   Part.optional [51, 56, 57] record.discretionPegOffset,
   Part.optional [56, 48, 50, 48] record.randomReserves,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 48, 48, 51] record.handleInst,
   Part.optional [50, 48, 49, 48, 55] record.groupID,
   Part.optional [50, 49, 48, 48, 50] record.locateBroker]

def ExecutionReportFilledOrBrokenTrade.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 48, 57]], [[51, 50]], [[51, 49]], [[52, 55]], [[50, 57]], [[49, 49, 49]], [[49, 57]], [[55, 53]], [[57, 56, 56, 50]], [[51, 48]], [[50, 48, 48, 48, 49]], [[57, 51, 53, 53]], [[49, 49, 48]], [[50, 49, 49]], [[50, 48, 48, 48, 57]], [[51, 56, 56]], [[51, 56, 57]], [[56, 48, 50, 48]], [[49, 50, 54]], [[50, 48, 48, 48, 51]], [[50, 48, 49, 48, 55]], [[50, 49, 48, 48, 50]]]

theorem ExecutionReportFilledOrBrokenTrade.shape (record : ExecutionReportFilledOrBrokenTrade) : record.parts.map Part.tags = ExecutionReportFilledOrBrokenTrade.tags := rfl

def ExecutionReportFilledOrBrokenTrade.decode (tokens : List Token) : Option ExecutionReportFilledOrBrokenTrade := do
  let orderID ← readRequired [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let execRefID ← readOptional [49, 57] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let liquidityFlag ← readOptional [57, 56, 56, 50] tokens
  let lastExchange ← readOptional [51, 48] tokens
  let userRefNum ← readOptional [50, 48, 48, 48, 49] tokens
  let crossType ← readOptional [57, 51, 53, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegOffset ← readOptional [50, 49, 49] tokens
  let discretionPrice ← readOptional [50, 48, 48, 48, 57] tokens
  let discretionPriceType ← readOptional [51, 56, 56] tokens
  let discretionPegOffset ← readOptional [51, 56, 57] tokens
  let randomReserves ← readOptional [56, 48, 50, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let handleInst ← readOptional [50, 48, 48, 48, 51] tokens
  let groupID ← readOptional [50, 48, 49, 48, 55] tokens
  let locateBroker ← readOptional [50, 49, 48, 48, 50] tokens
  pure { orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, execRefID, tradeDate, liquidityFlag, lastExchange, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker }

theorem ExecutionReportFilledOrBrokenTrade.decode_agrees (record : ExecutionReportFilledOrBrokenTrade) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFilledOrBrokenTrade.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFilledOrBrokenTrade.decode tokens = some record := by
  have distinct : ExecutionReportFilledOrBrokenTrade.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have liquidityFlag := readOptional_part [57, 56, 56, 50] record.liquidityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have lastExchange := readOptional_part [51, 48] record.lastExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have userRefNum := readOptional_part [50, 48, 48, 48, 49] record.userRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have crossType := readOptional_part [57, 51, 53, 53] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have pegOffset := readOptional_part [50, 49, 49] record.pegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have discretionPrice := readOptional_part [50, 48, 48, 48, 57] record.discretionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have discretionPriceType := readOptional_part [51, 56, 56] record.discretionPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have discretionPegOffset := readOptional_part [51, 56, 57] record.discretionPegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have randomReserves := readOptional_part [56, 48, 50, 48] record.randomReserves tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have handleInst := readOptional_part [50, 48, 48, 48, 51] record.handleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have groupID := readOptional_part [50, 48, 49, 48, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have locateBroker := readOptional_part [50, 49, 48, 48, 50] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [ExecutionReportFilledOrBrokenTrade.decode, orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, execRefID, tradeDate, liquidityFlag, lastExchange, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker, some_bind] <;> rfl

theorem ExecutionReportFilledOrBrokenTrade.taken (record : ExecutionReportFilledOrBrokenTrade) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.liquidityFlag (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastExchange (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.userRefNum (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffset (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 57] record.discretionPrice (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionPriceType (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionPegOffset (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.randomReserves (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.handleInst (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 48, 55] record.groupID (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48, 48, 50] record.locateBroker (by decide) (by decide))
                         (paired_none pairing)))))))))))))))))))))))

structure ExecutionReportOrderCancel where
  orderID : Terminated 1  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  maxFloor : Option (Terminated 1)  -- tag 111
  userRefNum : Option (Terminated 1)  -- tag 20001
  crossType : Option (Terminated 1)  -- tag 9355
  minQty : Option (Terminated 1)  -- tag 110
  pegOffset : Option (Terminated 1)  -- tag 211
  discretionPrice : Option (Terminated 1)  -- tag 20009
  discretionPriceType : Option (Terminated 1)  -- tag 388
  discretionPegOffset : Option (Terminated 1)  -- tag 389
  randomReserves : Option (Terminated 1)  -- tag 8020
  expireTime : Option (Terminated 1)  -- tag 126
  handleInst : Option (Terminated 1)  -- tag 20003
  groupID : Option (Terminated 1)  -- tag 20107
  locateBroker : Option (Terminated 1)  -- tag 21002

def ExecutionReportOrderCancel.parts (record : ExecutionReportOrderCancel) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 48, 48, 48, 49] record.userRefNum,
   Part.optional [57, 51, 53, 53] record.crossType,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegOffset,
   Part.optional [50, 48, 48, 48, 57] record.discretionPrice,
   Part.optional [51, 56, 56] record.discretionPriceType,
   Part.optional [51, 56, 57] record.discretionPegOffset,
   Part.optional [56, 48, 50, 48] record.randomReserves,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 48, 48, 51] record.handleInst,
   Part.optional [50, 48, 49, 48, 55] record.groupID,
   Part.optional [50, 49, 48, 48, 50] record.locateBroker]

def ExecutionReportOrderCancel.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 48, 57]], [[51, 50]], [[51, 49]], [[52, 55]], [[50, 57]], [[49, 49, 49]], [[50, 48, 48, 48, 49]], [[57, 51, 53, 53]], [[49, 49, 48]], [[50, 49, 49]], [[50, 48, 48, 48, 57]], [[51, 56, 56]], [[51, 56, 57]], [[56, 48, 50, 48]], [[49, 50, 54]], [[50, 48, 48, 48, 51]], [[50, 48, 49, 48, 55]], [[50, 49, 48, 48, 50]]]

theorem ExecutionReportOrderCancel.shape (record : ExecutionReportOrderCancel) : record.parts.map Part.tags = ExecutionReportOrderCancel.tags := rfl

def ExecutionReportOrderCancel.decode (tokens : List Token) : Option ExecutionReportOrderCancel := do
  let orderID ← readRequired [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let userRefNum ← readOptional [50, 48, 48, 48, 49] tokens
  let crossType ← readOptional [57, 51, 53, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegOffset ← readOptional [50, 49, 49] tokens
  let discretionPrice ← readOptional [50, 48, 48, 48, 57] tokens
  let discretionPriceType ← readOptional [51, 56, 56] tokens
  let discretionPegOffset ← readOptional [51, 56, 57] tokens
  let randomReserves ← readOptional [56, 48, 50, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let handleInst ← readOptional [50, 48, 48, 48, 51] tokens
  let groupID ← readOptional [50, 48, 49, 48, 55] tokens
  let locateBroker ← readOptional [50, 49, 48, 48, 50] tokens
  pure { orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker }

theorem ExecutionReportOrderCancel.decode_agrees (record : ExecutionReportOrderCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportOrderCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOrderCancel.decode tokens = some record := by
  have distinct : ExecutionReportOrderCancel.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have userRefNum := readOptional_part [50, 48, 48, 48, 49] record.userRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have crossType := readOptional_part [57, 51, 53, 53] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffset := readOptional_part [50, 49, 49] record.pegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have discretionPrice := readOptional_part [50, 48, 48, 48, 57] record.discretionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have discretionPriceType := readOptional_part [51, 56, 56] record.discretionPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have discretionPegOffset := readOptional_part [51, 56, 57] record.discretionPegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have randomReserves := readOptional_part [56, 48, 50, 48] record.randomReserves tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have handleInst := readOptional_part [50, 48, 48, 48, 51] record.handleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have groupID := readOptional_part [50, 48, 49, 48, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have locateBroker := readOptional_part [50, 49, 48, 48, 50] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [ExecutionReportOrderCancel.decode, orderID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, userRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, locateBroker, some_bind] <;> rfl

theorem ExecutionReportOrderCancel.taken (record : ExecutionReportOrderCancel) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.userRefNum (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffset (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 57] record.discretionPrice (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionPriceType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionPegOffset (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.randomReserves (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.handleInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 48, 55] record.groupID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48, 48, 50] record.locateBroker (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

structure ExecutionReportOrderReplace where
  origClOrdID : Terminated 1  -- tag 41
  clientID : Option (Terminated 1)  -- tag 109
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  maxFloor : Option (Terminated 1)  -- tag 111
  origUserRefNum : Option (Terminated 1)  -- tag 20007
  crossType : Option (Terminated 1)  -- tag 9355
  minQty : Option (Terminated 1)  -- tag 110
  pegOffset : Option (Terminated 1)  -- tag 211
  discretionPrice : Option (Terminated 1)  -- tag 20009
  discretionPriceType : Option (Terminated 1)  -- tag 388
  discretionPegOffset : Option (Terminated 1)  -- tag 389
  randomReserves : Option (Terminated 1)  -- tag 8020
  expireTime : Option (Terminated 1)  -- tag 126
  handleInst : Option (Terminated 1)  -- tag 20003
  groupID : Option (Terminated 1)  -- tag 20107
  userRefNum : Option (Terminated 1)  -- tag 20001
  displayInstruction : Option (Terminated 1)  -- tag 9140
  locateBroker : Option (Terminated 1)  -- tag 21002

def ExecutionReportOrderReplace.parts (record : ExecutionReportOrderReplace) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [50, 48, 48, 48, 55] record.origUserRefNum,
   Part.optional [57, 51, 53, 53] record.crossType,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [50, 49, 49] record.pegOffset,
   Part.optional [50, 48, 48, 48, 57] record.discretionPrice,
   Part.optional [51, 56, 56] record.discretionPriceType,
   Part.optional [51, 56, 57] record.discretionPegOffset,
   Part.optional [56, 48, 50, 48] record.randomReserves,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 48, 48, 51] record.handleInst,
   Part.optional [50, 48, 49, 48, 55] record.groupID,
   Part.optional [50, 48, 48, 48, 49] record.userRefNum,
   Part.optional [57, 49, 52, 48] record.displayInstruction,
   Part.optional [50, 49, 48, 48, 50] record.locateBroker]

def ExecutionReportOrderReplace.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 48, 57]], [[51, 50]], [[51, 49]], [[52, 55]], [[50, 57]], [[49, 49, 49]], [[50, 48, 48, 48, 55]], [[57, 51, 53, 53]], [[49, 49, 48]], [[50, 49, 49]], [[50, 48, 48, 48, 57]], [[51, 56, 56]], [[51, 56, 57]], [[56, 48, 50, 48]], [[49, 50, 54]], [[50, 48, 48, 48, 51]], [[50, 48, 49, 48, 55]], [[50, 48, 48, 48, 49]], [[57, 49, 52, 48]], [[50, 49, 48, 48, 50]]]

theorem ExecutionReportOrderReplace.shape (record : ExecutionReportOrderReplace) : record.parts.map Part.tags = ExecutionReportOrderReplace.tags := rfl

def ExecutionReportOrderReplace.decode (tokens : List Token) : Option ExecutionReportOrderReplace := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let origUserRefNum ← readOptional [50, 48, 48, 48, 55] tokens
  let crossType ← readOptional [57, 51, 53, 53] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let pegOffset ← readOptional [50, 49, 49] tokens
  let discretionPrice ← readOptional [50, 48, 48, 48, 57] tokens
  let discretionPriceType ← readOptional [51, 56, 56] tokens
  let discretionPegOffset ← readOptional [51, 56, 57] tokens
  let randomReserves ← readOptional [56, 48, 50, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let handleInst ← readOptional [50, 48, 48, 48, 51] tokens
  let groupID ← readOptional [50, 48, 49, 48, 55] tokens
  let userRefNum ← readOptional [50, 48, 48, 48, 49] tokens
  let displayInstruction ← readOptional [57, 49, 52, 48] tokens
  let locateBroker ← readOptional [50, 49, 48, 48, 50] tokens
  pure { origClOrdID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, origUserRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, userRefNum, displayInstruction, locateBroker }

theorem ExecutionReportOrderReplace.decode_agrees (record : ExecutionReportOrderReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportOrderReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportOrderReplace.decode tokens = some record := by
  have distinct : ExecutionReportOrderReplace.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origUserRefNum := readOptional_part [50, 48, 48, 48, 55] record.origUserRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have crossType := readOptional_part [57, 51, 53, 53] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffset := readOptional_part [50, 49, 49] record.pegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have discretionPrice := readOptional_part [50, 48, 48, 48, 57] record.discretionPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have discretionPriceType := readOptional_part [51, 56, 56] record.discretionPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have discretionPegOffset := readOptional_part [51, 56, 57] record.discretionPegOffset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have randomReserves := readOptional_part [56, 48, 50, 48] record.randomReserves tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have handleInst := readOptional_part [50, 48, 48, 48, 51] record.handleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have groupID := readOptional_part [50, 48, 49, 48, 55] record.groupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have userRefNum := readOptional_part [50, 48, 48, 48, 49] record.userRefNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have displayInstruction := readOptional_part [57, 49, 52, 48] record.displayInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have locateBroker := readOptional_part [50, 49, 48, 48, 50] record.locateBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  simp only [ExecutionReportOrderReplace.decode, origClOrdID, clientID, lastShares, lastPx, rule80A, lastCapacity, maxFloor, origUserRefNum, crossType, minQty, pegOffset, discretionPrice, discretionPriceType, discretionPegOffset, randomReserves, expireTime, handleInst, groupID, userRefNum, displayInstruction, locateBroker, some_bind] <;> rfl

theorem ExecutionReportOrderReplace.taken (record : ExecutionReportOrderReplace) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 55] record.origUserRefNum (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffset (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 57] record.discretionPrice (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 56] record.discretionPriceType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 56, 57] record.discretionPegOffset (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.randomReserves (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 51] record.handleInst (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 48, 55] record.groupID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 49] record.userRefNum (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [57, 49, 52, 48] record.displayInstruction (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48, 48, 50] record.locateBroker (by decide) (by decide))
                       (paired_none pairing)))))))))))))))))))))

structure ExecutionReportRejectedOrder where
  orderID : Terminated 1  -- tag 37
  limitPrice : Option (Terminated 1)  -- tag 99

def ExecutionReportRejectedOrder.parts (record : ExecutionReportRejectedOrder) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.optional [57, 57] record.limitPrice]

def ExecutionReportRejectedOrder.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[57, 57]]]

theorem ExecutionReportRejectedOrder.shape (record : ExecutionReportRejectedOrder) : record.parts.map Part.tags = ExecutionReportRejectedOrder.tags := rfl

def ExecutionReportRejectedOrder.decode (tokens : List Token) : Option ExecutionReportRejectedOrder := do
  let orderID ← readRequired [51, 55] tokens
  let limitPrice ← readOptional [57, 57] tokens
  pure { orderID, limitPrice }

theorem ExecutionReportRejectedOrder.decode_agrees (record : ExecutionReportRejectedOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRejectedOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRejectedOrder.decode tokens = some record := by
  have distinct : ExecutionReportRejectedOrder.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have limitPrice := readOptional_part [57, 57] record.limitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRejectedOrder.decode, orderID, limitPrice, some_bind] <;> rfl

theorem ExecutionReportRejectedOrder.taken (record : ExecutionReportRejectedOrder) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.limitPrice (by decide) (by decide))
    (paired_none pairing))

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

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

structure Logon where
  encryptMethod : Option (Terminated 1)  -- tag 98
  heartBtInt : Terminated 1  -- tag 108

def Logon.parts (record : Logon) : List Part :=
  [Part.optional [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readOptional [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  pure { encryptMethod, heartBtInt }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readOptional_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_none pairing))

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

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

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

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_none pairing)))))

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

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
    (paired_none pairing))

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

theorem TestRequest.taken (record : TestRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

inductive Message where
  | executionReportOrderAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderAcknowledgement)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFilledOrBrokenTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFilledOrBrokenTrade)
  | executionReportOrderCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderCancel)
  | executionReportOrderReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderReplace)
  | executionReportRejectedOrder (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectedOrder)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .executionReportOrderAcknowledgement header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFilledOrBrokenTrade header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportOrderCancel header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportOrderReplace header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
  | .executionReportRejectedOrder header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [48] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderAcknowledgement.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOrderAcknowledgement.decode rest
              pure (.executionReportOrderAcknowledgement header r0 r1)
            else none
          else if key.val = [49] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPartialFill.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPartialFill.decode rest
              pure (.executionReportPartialFill header r0 r1)
            else none
          else if key.val = [50] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFilledOrBrokenTrade.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportFilledOrBrokenTrade.decode rest
              pure (.executionReportFilledOrBrokenTrade header r0 r1)
            else none
          else if key.val = [52] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderCancel.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOrderCancel.decode rest
              pure (.executionReportOrderCancel header r0 r1)
            else none
          else if key.val = [53] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderReplace.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportOrderReplace.decode rest
              pure (.executionReportOrderReplace header r0 r1)
            else none
          else if key.val = [56] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectedOrder.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportRejectedOrder.decode rest
              pure (.executionReportRejectedOrder header r0 r1)
            else none
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
      else none
    else none

theorem Message.decode_executionReportOrderAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderAcknowledgement) :
    Message.decode (Message.tokens (.executionReportOrderAcknowledgement header r0 r1)) = some (.executionReportOrderAcknowledgement header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOrderAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOrderAcknowledgement.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOrderAcknowledgement.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOrderAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderAcknowledgement.tags) rfl
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

theorem Message.decode_executionReportFilledOrBrokenTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFilledOrBrokenTrade) :
    Message.decode (Message.tokens (.executionReportFilledOrBrokenTrade header r0 r1)) = some (.executionReportFilledOrBrokenTrade header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFilledOrBrokenTrade.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportFilledOrBrokenTrade.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportFilledOrBrokenTrade.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportFilledOrBrokenTrade.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportFilledOrBrokenTrade.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFilledOrBrokenTrade.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportOrderCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderCancel) :
    Message.decode (Message.tokens (.executionReportOrderCancel header r0 r1)) = some (.executionReportOrderCancel header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderCancel.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOrderCancel.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOrderCancel.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOrderCancel.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOrderCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderCancel.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportOrderReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderReplace) :
    Message.decode (Message.tokens (.executionReportOrderReplace header r0 r1)) = some (.executionReportOrderReplace header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderReplace.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportOrderReplace.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportOrderReplace.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportOrderReplace.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportOrderReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportOrderReplace.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRejectedOrder (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectedOrder) :
    Message.decode (Message.tokens (.executionReportRejectedOrder header r0 r1)) = some (.executionReportRejectedOrder header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectedOrder.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportRejectedOrder.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportRejectedOrder.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRejectedOrder.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportRejectedOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRejectedOrder.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

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
  | executionReportOrderAcknowledgement header r0 r1 => exact Message.decode_executionReportOrderAcknowledgement header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFilledOrBrokenTrade header r0 r1 => exact Message.decode_executionReportFilledOrBrokenTrade header r0 r1
  | executionReportOrderCancel header r0 r1 => exact Message.decode_executionReportOrderCancel header r0 r1
  | executionReportOrderReplace header r0 r1 => exact Message.decode_executionReportOrderReplace header r0 r1
  | executionReportRejectedOrder header r0 r1 => exact Message.decode_executionReportRejectedOrder header r0 r1
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportOrderAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderAcknowledgement) :
    Message.decodeBytes (Message.encode (.executionReportOrderAcknowledgement header r0 r1)) = some (.executionReportOrderAcknowledgement header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportOrderAcknowledgement.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOrderAcknowledgement header r0 r1

theorem Message.decodeBytes_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decodeBytes (Message.encode (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[49], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[49], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportPartialFill.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPartialFill header r0 r1

theorem Message.decodeBytes_executionReportFilledOrBrokenTrade (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFilledOrBrokenTrade) :
    Message.decodeBytes (Message.encode (.executionReportFilledOrBrokenTrade header r0 r1)) = some (.executionReportFilledOrBrokenTrade header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[50], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportFilledOrBrokenTrade.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFilledOrBrokenTrade header r0 r1

theorem Message.decodeBytes_executionReportOrderCancel (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderCancel) :
    Message.decodeBytes (Message.encode (.executionReportOrderCancel header r0 r1)) = some (.executionReportOrderCancel header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[52], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[52], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportOrderCancel.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOrderCancel header r0 r1

theorem Message.decodeBytes_executionReportOrderReplace (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportOrderReplace) :
    Message.decodeBytes (Message.encode (.executionReportOrderReplace header r0 r1)) = some (.executionReportOrderReplace header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[53], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[53], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportOrderReplace.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportOrderReplace header r0 r1

theorem Message.decodeBytes_executionReportRejectedOrder (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportRejectedOrder) :
    Message.decodeBytes (Message.encode (.executionReportRejectedOrder header r0 r1)) = some (.executionReportRejectedOrder header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[56], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[56], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRejectedOrder.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRejectedOrder header r0 r1

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportOrderAcknowledgement header r0 r1 => exact Message.decodeBytes_executionReportOrderAcknowledgement header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFilledOrBrokenTrade header r0 r1 => exact Message.decodeBytes_executionReportFilledOrBrokenTrade header r0 r1
  | executionReportOrderCancel header r0 r1 => exact Message.decodeBytes_executionReportOrderCancel header r0 r1
  | executionReportOrderReplace header r0 r1 => exact Message.decodeBytes_executionReportOrderReplace header r0 r1
  | executionReportRejectedOrder header r0 r1 => exact Message.decodeBytes_executionReportRejectedOrder header r0 r1
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue states it: one of FIX.4.0, FIX.4.1, FIX.4.2, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 48], [70, 73, 88, 46, 52, 46, 49], [70, 73, 88, 46, 52, 46, 50]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.NasdaqNtxequitiesCoredropcopyFixV1002026Exchange
