import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqPsxequitiesCoredropcopyFixV10Exchange

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

structure Heartbeat

def Heartbeat.parts (_ : Heartbeat) : List Part :=
  []

def Heartbeat.tags : List (List (List UInt8)) :=
  []

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (_ : List Token) : Option Heartbeat := some {}

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (_ : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure ExecutionReport where
  deliverToCompID : Option (Terminated 1)  -- tag 128
  targetSubID : Terminated 1  -- tag 57
  senderSubID : Terminated 1  -- tag 50
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  ordStatus : Terminated 1  -- tag 39
  clientID : Option (Terminated 1)  -- tag 109
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  leavesQty : Option (Terminated 1)  -- tag 151
  cumQty : Terminated 1  -- tag 14
  avgPx : Terminated 1  -- tag 6
  price : Option (Terminated 1)  -- tag 44
  ordType : Option (Terminated 1)  -- tag 40
  rule80A : Option (Terminated 1)  -- tag 47
  lastCapacity : Option (Terminated 1)  -- tag 29
  execBroker : Option (Terminated 1)  -- tag 76
  maxFloor : Option (Terminated 1)  -- tag 111
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Option (Terminated 1)  -- tag 59
  execRefID : Option (Terminated 1)  -- tag 19
  tradeDate : Option (Terminated 1)  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  liquidityFlag : Option (Terminated 1)  -- tag 9882
  lastExchange : Option (Terminated 1)  -- tag 30
  customerType : Option (Terminated 1)  -- tag 20006
  intraDayIndicativePrice : Option (Terminated 1)  -- tag 20007

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [49, 50, 56] record.deliverToCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [53, 48] record.senderSubID,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [54] record.avgPx,
   Part.optional [52, 52] record.price,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 57] record.lastCapacity,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 57] record.execRefID,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [57, 56, 56, 50] record.liquidityFlag,
   Part.optional [51, 48] record.lastExchange,
   Part.optional [50, 48, 48, 48, 54] record.customerType,
   Part.optional [50, 48, 48, 48, 55] record.intraDayIndicativePrice]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[49, 50, 56]], [[53, 55]], [[53, 48]], [[49]], [[49, 49]], [[51, 55]], [[49, 55]], [[50, 48]], [[51, 57]], [[49, 48, 57]], [[53, 53]], [[53, 52]], [[51, 56]], [[49, 53, 49]], [[49, 52]], [[54]], [[52, 52]], [[52, 48]], [[52, 55]], [[50, 57]], [[55, 54]], [[49, 49, 49]], [[49, 56]], [[53, 57]], [[49, 57]], [[55, 53]], [[54, 48]], [[57, 56, 56, 50]], [[51, 48]], [[50, 48, 48, 48, 54]], [[50, 48, 48, 48, 55]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let avgPx ← readRequired [54] tokens
  let price ← readOptional [52, 52] tokens
  let ordType ← readOptional [52, 48] tokens
  let rule80A ← readOptional [52, 55] tokens
  let lastCapacity ← readOptional [50, 57] tokens
  let execBroker ← readOptional [55, 54] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let execRefID ← readOptional [49, 57] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let liquidityFlag ← readOptional [57, 56, 56, 50] tokens
  let lastExchange ← readOptional [51, 48] tokens
  let customerType ← readOptional [50, 48, 48, 48, 54] tokens
  let intraDayIndicativePrice ← readOptional [50, 48, 48, 48, 55] tokens
  pure { deliverToCompID, targetSubID, senderSubID, account, clOrdID, orderID, execID, execTransType, ordStatus, clientID, symbol, side, orderQty, leavesQty, cumQty, avgPx, price, ordType, rule80A, lastCapacity, execBroker, maxFloor, execInst, timeInForce, execRefID, tradeDate, transactTime, liquidityFlag, lastExchange, customerType, intraDayIndicativePrice }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have lastCapacity := readOptional_part [50, 57] record.lastCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have execRefID := readOptional_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have liquidityFlag := readOptional_part [57, 56, 56, 50] record.liquidityFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have lastExchange := readOptional_part [51, 48] record.lastExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have customerType := readOptional_part [50, 48, 48, 48, 54] record.customerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have intraDayIndicativePrice := readOptional_part [50, 48, 48, 48, 55] record.intraDayIndicativePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [ExecutionReport.decode, deliverToCompID, targetSubID, senderSubID, account, clOrdID, orderID, execID, execTransType, ordStatus, clientID, symbol, side, orderQty, leavesQty, cumQty, avgPx, price, ordType, rule80A, lastCapacity, execBroker, maxFloor, execInst, timeInForce, execRefID, tradeDate, transactTime, liquidityFlag, lastExchange, customerType, intraDayIndicativePrice, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 48] record.senderSubID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 57] record.lastCapacity (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 57] record.execRefID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.liquidityFlag (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastExchange (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 54] record.customerType (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 55] record.intraDayIndicativePrice (by decide) (by decide))
                                 (paired_none pairing)))))))))))))))))))))))))))))))

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

theorem ExecutionReportNew.taken (record : ExecutionReportNew) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure ExecutionReportPartialFill where
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31

def ExecutionReportPartialFill.parts (record : ExecutionReportPartialFill) : List Part :=
  [Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx]

def ExecutionReportPartialFill.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]]]

theorem ExecutionReportPartialFill.shape (record : ExecutionReportPartialFill) : record.parts.map Part.tags = ExecutionReportPartialFill.tags := rfl

def ExecutionReportPartialFill.decode (tokens : List Token) : Option ExecutionReportPartialFill := do
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  pure { lastShares, lastPx }

theorem ExecutionReportPartialFill.decode_agrees (record : ExecutionReportPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportPartialFill.tags.flatten.Nodup := by decide +kernel
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportPartialFill.decode, lastShares, lastPx, some_bind] <;> rfl

theorem ExecutionReportPartialFill.taken (record : ExecutionReportPartialFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_none pairing))

structure ExecutionReportFill where
  lastShares : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31

def ExecutionReportFill.parts (record : ExecutionReportFill) : List Part :=
  [Part.required [51, 50] record.lastShares,
   Part.required [51, 49] record.lastPx]

def ExecutionReportFill.tags : List (List (List UInt8)) :=
  [[[51, 50]], [[51, 49]]]

theorem ExecutionReportFill.shape (record : ExecutionReportFill) : record.parts.map Part.tags = ExecutionReportFill.tags := rfl

def ExecutionReportFill.decode (tokens : List Token) : Option ExecutionReportFill := do
  let lastShares ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  pure { lastShares, lastPx }

theorem ExecutionReportFill.decode_agrees (record : ExecutionReportFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFill.decode tokens = some record := by
  have distinct : ExecutionReportFill.tags.flatten.Nodup := by decide +kernel
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportFill.decode, lastShares, lastPx, some_bind] <;> rfl

theorem ExecutionReportFill.taken (record : ExecutionReportFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_none pairing))

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

theorem ExecutionReportCanceled.taken (record : ExecutionReportCanceled) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_none pairing))

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

theorem ExecutionReportReplaced.taken (record : ExecutionReportReplaced) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_none pairing)

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew)
  | executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill)
  | executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill)
  | executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled)
  | executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReportNew header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
  | .executionReportPartialFill header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
  | .executionReportFill header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
  | .executionReportCanceled header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
  | .executionReportReplaced header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [56] then
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
          else none
      else none
    else none

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decode (Message.tokens (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportNew.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | executionReportNew header r0 r1 => exact Message.decode_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decode_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decode_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decode_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decode_executionReportReplaced header r0 r1

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_executionReportNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportNew) :
    Message.decodeBytes (Message.encode (.executionReportNew header r0 r1)) = some (.executionReportNew header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportNew.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportNew header r0 r1

theorem Message.decodeBytes_executionReportPartialFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPartialFill) :
    Message.decodeBytes (Message.encode (.executionReportPartialFill header r0 r1)) = some (.executionReportPartialFill header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[49], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[49], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportPartialFill.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPartialFill header r0 r1

theorem Message.decodeBytes_executionReportFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFill) :
    Message.decodeBytes (Message.encode (.executionReportFill header r0 r1)) = some (.executionReportFill header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[50], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportFill.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFill header r0 r1

theorem Message.decodeBytes_executionReportCanceled (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCanceled) :
    Message.decodeBytes (Message.encode (.executionReportCanceled header r0 r1)) = some (.executionReportCanceled header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[52], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[52], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportCanceled.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCanceled header r0 r1

theorem Message.decodeBytes_executionReportReplaced (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportReplaced) :
    Message.decodeBytes (Message.encode (.executionReportReplaced header r0 r1)) = some (.executionReportReplaced header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[53], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[53], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportReplaced.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportReplaced header r0 r1

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | executionReportNew header r0 r1 => exact Message.decodeBytes_executionReportNew header r0 r1
  | executionReportPartialFill header r0 r1 => exact Message.decodeBytes_executionReportPartialFill header r0 r1
  | executionReportFill header r0 r1 => exact Message.decodeBytes_executionReportFill header r0 r1
  | executionReportCanceled header r0 r1 => exact Message.decodeBytes_executionReportCanceled header r0 r1
  | executionReportReplaced header r0 r1 => exact Message.decodeBytes_executionReportReplaced header r0 r1

/-- BeginString as the venue states it: one of FIX.4.0, FIX.4.1, FIX.4.2, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 48], [70, 73, 88, 46, 52, 46, 49], [70, 73, 88, 46, 52, 46, 50]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.NasdaqPsxequitiesCoredropcopyFixV10Exchange
