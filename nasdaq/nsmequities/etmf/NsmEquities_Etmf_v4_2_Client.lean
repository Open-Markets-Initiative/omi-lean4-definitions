import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v4.2, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNsmequitiesEtmfFixV42Client

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  sendingTime : Terminated 1  -- tag 52
  senderSubID : Option (Terminated 1)  -- tag 50
  targetSubID : Option (Terminated 1)  -- tag 57
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 50] record.sendingTime,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 57]], [[53, 54]], [[53, 50]], [[53, 48]], [[53, 55]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, senderCompID, targetCompID, sendingTime, senderSubID, targetSubID, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, senderCompID, targetCompID, sendingTime, senderSubID, targetSubID, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
           (paired_none pairing)))))))))

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  rawData : Option (List UInt8)  -- tag 96

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.dataOptional [57, 53] [57, 54] record.rawData]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[49, 52, 49]], [[57, 53], [57, 54]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  pure { encryptMethod, heartBtInt, resetSeqNumFlag, rawData }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have rawData := readDataOptional_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, resetSeqNumFlag, rawData, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
      (paired_none pairing))))

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

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  handlInst : Terminated 1  -- tag 21
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  clientID : Option (Terminated 1)  -- tag 109
  execBroker : Option (Terminated 1)  -- tag 76
  account : Option (Terminated 1)  -- tag 1
  settlmntTyp : Option (Terminated 1)  -- tag 63
  futSettDate : Option (Terminated 1)  -- tag 64
  execInst : Option (Terminated 1)  -- tag 18
  displayInst : Option (Terminated 1)  -- tag 9140
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  locateReqd : Option (Terminated 1)  -- tag 114
  timeInForce : Option (Terminated 1)  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  pegDifference : Option (Terminated 1)  -- tag 211
  text : Option (Terminated 1)  -- tag 58
  expireTime : Option (Terminated 1)  -- tag 126
  marketabilityInstructions : Option (Terminated 1)  -- tag 9395
  displayRange : Option (Terminated 1)  -- tag 8020
  displayExecInst : Option (Terminated 1)  -- tag 9391
  displayPrice : Option (Terminated 1)  -- tag 9392
  displayPegDifference : Option (Terminated 1)  -- tag 9396
  crossTradeFlag : Option (Terminated 1)  -- tag 9355
  deliverToSubID : Option (Terminated 1)  -- tag 129
  customerType : Option (Terminated 1)  -- tag 20006

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [50, 49] record.handlInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49] record.account,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 52] record.futSettDate,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 49, 52, 48] record.displayInst,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [53, 56] record.text,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [57, 51, 57, 53] record.marketabilityInstructions,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 51, 57, 49] record.displayExecInst,
   Part.optional [57, 51, 57, 50] record.displayPrice,
   Part.optional [57, 51, 57, 54] record.displayPegDifference,
   Part.optional [57, 51, 53, 53] record.crossTradeFlag,
   Part.optional [49, 50, 57] record.deliverToSubID,
   Part.optional [50, 48, 48, 48, 54] record.customerType]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[50, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 48, 57]], [[55, 54]], [[49]], [[54, 51]], [[54, 52]], [[49, 56]], [[57, 49, 52, 48]], [[49, 49, 48]], [[49, 49, 49]], [[49, 49, 52]], [[53, 57]], [[52, 55]], [[50, 49, 49]], [[53, 56]], [[49, 50, 54]], [[57, 51, 57, 53]], [[56, 48, 50, 48]], [[57, 51, 57, 49]], [[57, 51, 57, 50]], [[57, 51, 57, 54]], [[57, 51, 53, 53]], [[49, 50, 57]], [[50, 48, 48, 48, 54]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let handlInst ← readRequired [50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let execBroker ← readOptional [55, 54] tokens
  let account ← readOptional [49] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let futSettDate ← readOptional [54, 52] tokens
  let execInst ← readOptional [49, 56] tokens
  let displayInst ← readOptional [57, 49, 52, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let text ← readOptional [53, 56] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let marketabilityInstructions ← readOptional [57, 51, 57, 53] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let displayExecInst ← readOptional [57, 51, 57, 49] tokens
  let displayPrice ← readOptional [57, 51, 57, 50] tokens
  let displayPegDifference ← readOptional [57, 51, 57, 54] tokens
  let crossTradeFlag ← readOptional [57, 51, 53, 53] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  let customerType ← readOptional [50, 48, 48, 48, 54] tokens
  pure { clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, execBroker, account, settlmntTyp, futSettDate, execInst, displayInst, minQty, maxFloor, locateReqd, timeInForce, rule80A, pegDifference, text, expireTime, marketabilityInstructions, displayRange, displayExecInst, displayPrice, displayPegDifference, crossTradeFlag, deliverToSubID, customerType }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have futSettDate := readOptional_part [54, 52] record.futSettDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayInst := readOptional_part [57, 49, 52, 48] record.displayInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have marketabilityInstructions := readOptional_part [57, 51, 57, 53] record.marketabilityInstructions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have displayExecInst := readOptional_part [57, 51, 57, 49] record.displayExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have displayPrice := readOptional_part [57, 51, 57, 50] record.displayPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have displayPegDifference := readOptional_part [57, 51, 57, 54] record.displayPegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have crossTradeFlag := readOptional_part [57, 51, 53, 53] record.crossTradeFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have customerType := readOptional_part [50, 48, 48, 48, 54] record.customerType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, execBroker, account, settlmntTyp, futSettDate, execInst, displayInst, minQty, maxFloor, locateReqd, timeInForce, rule80A, pegDifference, text, expireTime, marketabilityInstructions, displayRange, displayExecInst, displayPrice, displayPegDifference, crossTradeFlag, deliverToSubID, customerType, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlmntTyp (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.futSettDate (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [57, 49, 52, 48] record.displayInst (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52] record.locateReqd (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57, 53] record.marketabilityInstructions (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.displayRange (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57, 49] record.displayExecInst (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57, 50] record.displayPrice (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57, 54] record.displayPegDifference (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [57, 51, 53, 53] record.crossTradeFlag (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [49, 50, 57] record.deliverToSubID (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 54] record.customerType (by decide) (by decide))
                                (paired_none pairing))))))))))))))))))))))))))))))

structure OrderCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  orderID : Option (Terminated 1)  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[51, 55]], [[49, 48, 57]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let orderID ← readOptional [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  pure { origClOrdID, clOrdID, symbol, side, orderQty, orderID, clientID }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, origClOrdID, clOrdID, symbol, side, orderQty, orderID, clientID, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
         (paired_none pairing)))))))

structure OrderCancelReplaceRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  handlInst : Terminated 1  -- tag 21
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  locateReqd : Option (Terminated 1)  -- tag 114
  orderID : Option (Terminated 1)  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  execInst : Option (Terminated 1)  -- tag 18
  displayInst : Option (Terminated 1)  -- tag 9140
  timeInForce : Option (Terminated 1)  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  account : Option (Terminated 1)  -- tag 1
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.required [50, 49] record.handlInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 49, 52] record.locateReqd,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 56] record.execInst,
   Part.optional [57, 49, 52, 48] record.displayInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [49] record.account,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [[50, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 49, 52]], [[51, 55]], [[49, 48, 57]], [[49, 56]], [[57, 49, 52, 48]], [[53, 57]], [[52, 55]], [[49]], [[49, 49, 48]], [[49, 49, 49]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let handlInst ← readRequired [50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let locateReqd ← readOptional [49, 49, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let displayInst ← readOptional [57, 49, 52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let account ← readOptional [49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  pure { origClOrdID, clOrdID, handlInst, symbol, side, orderQty, ordType, price, locateReqd, orderID, clientID, execInst, displayInst, timeInForce, rule80A, account, minQty, maxFloor }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have locateReqd := readOptional_part [49, 49, 52] record.locateReqd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displayInst := readOptional_part [57, 49, 52, 48] record.displayInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, origClOrdID, clOrdID, handlInst, symbol, side, orderQty, ordType, price, locateReqd, orderID, clientID, execInst, displayInst, timeInForce, rule80A, account, minQty, maxFloor, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52] record.locateReqd (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 49, 52, 48] record.displayInst (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                    (paired_none pairing))))))))))))))))))

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
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

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

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
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0

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

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0

/-- BeginString as the venue states it: one of FIX.4.0, FIX.4.1, FIX.4.2, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 48], [70, 73, 88, 46, 52, 46, 49], [70, 73, 88, 46, 52, 46, 50]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.NasdaqNsmequitiesEtmfFixV42Client
