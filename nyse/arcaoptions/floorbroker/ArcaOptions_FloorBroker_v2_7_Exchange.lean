import Wire

/-!
# New York Stock Exchange NYSE Pillar Options Floor Broker OMS Open Outcry v2.7, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NyseArcaoptionsFloorbrokerFixV27Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

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
  deliverToCompID : Option (Terminated 1)  -- tag 128

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
   Part.optional [49, 50, 56] record.deliverToCompID]

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
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID }

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
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
              (paired_none pairing))))))))))))

structure ExecutionReport

def ExecutionReport.parts (_ : ExecutionReport) : List Part :=
  []

def ExecutionReport.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (_ : List Token) : Option ExecutionReport := some {}

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure NoTradingSessions where
  tradingSessionID : Terminated 1  -- tag 336

def NoTradingSessions.parts (record : NoTradingSessions) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID]

def NoTradingSessions.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]]]

theorem NoTradingSessions.shape (record : NoTradingSessions) : record.parts.map Part.tags = NoTradingSessions.tags := rfl

def NoTradingSessions.decode (tokens : List Token) : Option NoTradingSessions := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { tradingSessionID }

theorem NoTradingSessions.decode_agrees (record : NoTradingSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradingSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradingSessions.decode tokens = some record := by
  have distinct : NoTradingSessions.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTradingSessions.decode, tradingSessionID, some_bind] <;> rfl

theorem NoTradingSessions.taken (record : NoTradingSessions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
   (paired_none pairing)

def NoTradingSessions.members : List (List UInt8) := NoTradingSessions.tags.flatten

def NoTradingSessions.encode (entry : NoTradingSessions) : List Token := encodeParts entry.parts

theorem NoTradingSessions.decode_encode (entry : NoTradingSessions) : NoTradingSessions.decode entry.encode = some entry :=
  NoTradingSessions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradingSessions.within (entry : NoTradingSessions) : ∀ token ∈ entry.encode, token.tag ∈ NoTradingSessions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradingSessions.shape] at this

theorem NoTradingSessions.led (entry : NoTradingSessions) : Lead [51, 51, 54] entry.encode :=
  lead_parts [51, 51, 54] entry.tradingSessionID _ NoTradingSessions.tags.tail rfl (by decide +kernel)

structure ExecutionReportBrokerOpenOutcryAnnouncement where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportBrokerOpenOutcryAnnouncement.parts (record : ExecutionReportBrokerOpenOutcryAnnouncement) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportBrokerOpenOutcryAnnouncement.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportBrokerOpenOutcryAnnouncement.shape (record : ExecutionReportBrokerOpenOutcryAnnouncement) : record.parts.map Part.tags = ExecutionReportBrokerOpenOutcryAnnouncement.tags := rfl

def ExecutionReportBrokerOpenOutcryAnnouncement.decode (tokens : List Token) : Option ExecutionReportBrokerOpenOutcryAnnouncement := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportBrokerOpenOutcryAnnouncement.decode_agrees (record : ExecutionReportBrokerOpenOutcryAnnouncement) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportBrokerOpenOutcryAnnouncement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportBrokerOpenOutcryAnnouncement.decode tokens = some record := by
  have distinct : ExecutionReportBrokerOpenOutcryAnnouncement.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportBrokerOpenOutcryAnnouncement.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportBrokerOpenOutcryAnnouncement.taken (record : ExecutionReportBrokerOpenOutcryAnnouncement) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.parts (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.shape (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) : record.parts.map Part.tags = ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags := rfl

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode (tokens : List Token) : Option ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode_agrees (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode tokens = some record := by
  have distinct : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.taken (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.parts (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.shape (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) : record.parts.map Part.tags = ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags := rfl

def ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode (tokens : List Token) : Option ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode_agrees (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode tokens = some record := by
  have distinct : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.taken (record : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportTradingOfficialOpenOutcryUnapproval where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportTradingOfficialOpenOutcryUnapproval.parts (record : ExecutionReportTradingOfficialOpenOutcryUnapproval) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportTradingOfficialOpenOutcryUnapproval.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportTradingOfficialOpenOutcryUnapproval.shape (record : ExecutionReportTradingOfficialOpenOutcryUnapproval) : record.parts.map Part.tags = ExecutionReportTradingOfficialOpenOutcryUnapproval.tags := rfl

def ExecutionReportTradingOfficialOpenOutcryUnapproval.decode (tokens : List Token) : Option ExecutionReportTradingOfficialOpenOutcryUnapproval := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportTradingOfficialOpenOutcryUnapproval.decode_agrees (record : ExecutionReportTradingOfficialOpenOutcryUnapproval) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradingOfficialOpenOutcryUnapproval.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradingOfficialOpenOutcryUnapproval.decode tokens = some record := by
  have distinct : ExecutionReportTradingOfficialOpenOutcryUnapproval.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportTradingOfficialOpenOutcryUnapproval.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportTradingOfficialOpenOutcryUnapproval.taken (record : ExecutionReportTradingOfficialOpenOutcryUnapproval) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportTradingOfficialOpenOutcryUnannoucement where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportTradingOfficialOpenOutcryUnannoucement.parts (record : ExecutionReportTradingOfficialOpenOutcryUnannoucement) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportTradingOfficialOpenOutcryUnannoucement.shape (record : ExecutionReportTradingOfficialOpenOutcryUnannoucement) : record.parts.map Part.tags = ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags := rfl

def ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode (tokens : List Token) : Option ExecutionReportTradingOfficialOpenOutcryUnannoucement := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode_agrees (record : ExecutionReportTradingOfficialOpenOutcryUnannoucement) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode tokens = some record := by
  have distinct : ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportTradingOfficialOpenOutcryUnannoucement.taken (record : ExecutionReportTradingOfficialOpenOutcryUnannoucement) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  legRefID : Option (Terminated 1)  -- tag 654
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  bestBidQty : Option (Terminated 1)  -- tag 20028
  bestBidPrice : Option (Terminated 1)  -- tag 20029
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  bestOfferQty : Option (Terminated 1)  -- tag 20033
  bestOfferPrice : Option (Terminated 1)  -- tag 20034
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  protectedBestBid : Option (Terminated 1)  -- tag 20043
  protectedBestOffer : Option (Terminated 1)  -- tag 20044

def ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.parts (record : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 50, 56] record.bestBidQty,
   Part.optional [50, 48, 48, 50, 57] record.bestBidPrice,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 51] record.bestOfferQty,
   Part.optional [50, 48, 48, 51, 52] record.bestOfferPrice,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [50, 48, 48, 52, 51] record.protectedBestBid,
   Part.optional [50, 48, 48, 52, 52] record.protectedBestOffer]

def ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[55, 57, 50, 56]], [[54, 53, 52]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 50, 56]], [[50, 48, 48, 50, 57]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 51]], [[50, 48, 48, 51, 52]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[50, 48, 48, 52, 51]], [[50, 48, 48, 52, 52]]]

theorem ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.shape (record : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) : record.parts.map Part.tags = ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags := rfl

def ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode (tokens : List Token) : Option ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let bestBidQty ← readOptional [50, 48, 48, 50, 56] tokens
  let bestBidPrice ← readOptional [50, 48, 48, 50, 57] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let bestOfferQty ← readOptional [50, 48, 48, 51, 51] tokens
  let bestOfferPrice ← readOptional [50, 48, 48, 51, 52] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let protectedBestBid ← readOptional [50, 48, 48, 52, 51] tokens
  let protectedBestOffer ← readOptional [50, 48, 48, 52, 52] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer }

theorem ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode_agrees (record : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode tokens = some record := by
  have distinct : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have bestBidQty := readOptional_part [50, 48, 48, 50, 56] record.bestBidQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have bestBidPrice := readOptional_part [50, 48, 48, 50, 57] record.bestBidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have bestOfferQty := readOptional_part [50, 48, 48, 51, 51] record.bestOfferQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have bestOfferPrice := readOptional_part [50, 48, 48, 51, 52] record.bestOfferPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have protectedBestBid := readOptional_part [50, 48, 48, 52, 51] record.protectedBestBid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have protectedBestOffer := readOptional_part [50, 48, 48, 52, 52] record.protectedBestOffer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  simp only [ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode, account, clOrdID, cumQty, execID, execTransType, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, multilegReportingType, optionalData, selfTradeType, legRefID, specialOrdType, extendedExecInst, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, bestBidQty, bestBidPrice, percentageStrike, percentagePrice, tiedHedgeIndicator, bestOfferQty, bestOfferPrice, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, protectedBestBid, protectedBestOffer, some_bind] <;> rfl

theorem ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.taken (record : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 56] record.bestBidQty (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 57] record.bestBidPrice (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 51] record.bestOfferQty (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 52] record.bestOfferPrice (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 51] record.protectedBestBid (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 52] record.protectedBestOffer (by decide) (by decide))
                                                      (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportFLEXPriceRequest where
  clOrdID : Terminated 1  -- tag 11
  lastPx : Option (Terminated 1)  -- tag 31
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  referencePrice : Terminated 1  -- tag 20045
  refDealID : Option (Terminated 1)  -- tag 30002

def ExecutionReportFLEXPriceRequest.parts (record : ExecutionReportFLEXPriceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 49] record.lastPx,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.required [50, 48, 48, 52, 53] record.referencePrice,
   Part.optional [51, 48, 48, 48, 50] record.refDealID]

def ExecutionReportFLEXPriceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 53]], [[53, 56]], [[54, 48]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 52, 53]], [[51, 48, 48, 48, 50]]]

theorem ExecutionReportFLEXPriceRequest.shape (record : ExecutionReportFLEXPriceRequest) : record.parts.map Part.tags = ExecutionReportFLEXPriceRequest.tags := rfl

def ExecutionReportFLEXPriceRequest.decode (tokens : List Token) : Option ExecutionReportFLEXPriceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let lastPx ← readOptional [51, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let referencePrice ← readRequired [50, 48, 48, 52, 53] tokens
  let refDealID ← readOptional [51, 48, 48, 48, 50] tokens
  pure { clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, text, transactTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, referencePrice, refDealID }

theorem ExecutionReportFLEXPriceRequest.decode_agrees (record : ExecutionReportFLEXPriceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFLEXPriceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFLEXPriceRequest.decode tokens = some record := by
  have distinct : ExecutionReportFLEXPriceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have referencePrice := readRequired_part [50, 48, 48, 52, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have refDealID := readOptional_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [ExecutionReportFLEXPriceRequest.decode, clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, text, transactTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, referencePrice, refDealID, some_bind] <;> rfl

theorem ExecutionReportFLEXPriceRequest.taken (record : ExecutionReportFLEXPriceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
              (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
               (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 52, 53] record.referencePrice (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 48, 50] record.refDealID (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

structure ExecutionReportFLEXPriceReject where
  clOrdID : Terminated 1  -- tag 11
  lastPx : Option (Terminated 1)  -- tag 31
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  introducingBadgeID : Terminated 1  -- tag 9448
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  referencePrice : Terminated 1  -- tag 20045
  refDealID : Option (Terminated 1)  -- tag 30002

def ExecutionReportFLEXPriceReject.parts (record : ExecutionReportFLEXPriceReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 49] record.lastPx,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.required [50, 48, 48, 52, 53] record.referencePrice,
   Part.optional [51, 48, 48, 48, 50] record.refDealID]

def ExecutionReportFLEXPriceReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 53]], [[53, 56]], [[54, 48]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[57, 52, 52, 56]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 52, 53]], [[51, 48, 48, 48, 50]]]

theorem ExecutionReportFLEXPriceReject.shape (record : ExecutionReportFLEXPriceReject) : record.parts.map Part.tags = ExecutionReportFLEXPriceReject.tags := rfl

def ExecutionReportFLEXPriceReject.decode (tokens : List Token) : Option ExecutionReportFLEXPriceReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let lastPx ← readOptional [51, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let referencePrice ← readRequired [50, 48, 48, 52, 53] tokens
  let refDealID ← readOptional [51, 48, 48, 48, 50] tokens
  pure { clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, text, transactTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, referencePrice, refDealID }

theorem ExecutionReportFLEXPriceReject.decode_agrees (record : ExecutionReportFLEXPriceReject) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportFLEXPriceReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportFLEXPriceReject.decode tokens = some record := by
  have distinct : ExecutionReportFLEXPriceReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have referencePrice := readRequired_part [50, 48, 48, 52, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have refDealID := readOptional_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [ExecutionReportFLEXPriceReject.decode, clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, text, transactTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, noTradingSessions, introducingBadgeID, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, referencePrice, refDealID, some_bind] <;> rfl

theorem ExecutionReportFLEXPriceReject.taken (record : ExecutionReportFLEXPriceReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
              (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
               (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 52, 53] record.referencePrice (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 48, 50] record.refDealID (by decide) (by decide))
                     (paired_none pairing)))))))))))))))))))

structure NoContraBrokers where
  contraBroker : Terminated 1  -- tag 375
  contraTrader : Option (Terminated 1)  -- tag 337

def NoContraBrokers.parts (record : NoContraBrokers) : List Part :=
  [Part.required [51, 55, 53] record.contraBroker,
   Part.optional [51, 51, 55] record.contraTrader]

def NoContraBrokers.tags : List (List (List UInt8)) :=
  [[[51, 55, 53]], [[51, 51, 55]]]

theorem NoContraBrokers.shape (record : NoContraBrokers) : record.parts.map Part.tags = NoContraBrokers.tags := rfl

def NoContraBrokers.decode (tokens : List Token) : Option NoContraBrokers := do
  let contraBroker ← readRequired [51, 55, 53] tokens
  let contraTrader ← readOptional [51, 51, 55] tokens
  pure { contraBroker, contraTrader }

theorem NoContraBrokers.decode_agrees (record : NoContraBrokers) (tokens : List Token)
    (agrees : ∀ tags ∈ NoContraBrokers.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoContraBrokers.decode tokens = some record := by
  have distinct : NoContraBrokers.tags.flatten.Nodup := by decide +kernel
  have contraBroker := readRequired_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraTrader := readOptional_part [51, 51, 55] record.contraTrader tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoContraBrokers.decode, contraBroker, contraTrader, some_bind] <;> rfl

theorem NoContraBrokers.taken (record : NoContraBrokers) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 51, 55] record.contraTrader (by decide) (by decide))
    (paired_none pairing))

def NoContraBrokers.members : List (List UInt8) := NoContraBrokers.tags.flatten

def NoContraBrokers.encode (entry : NoContraBrokers) : List Token := encodeParts entry.parts

theorem NoContraBrokers.decode_encode (entry : NoContraBrokers) : NoContraBrokers.decode entry.encode = some entry :=
  NoContraBrokers.decode_agrees entry _ (fun _ _ => rfl)

theorem NoContraBrokers.within (entry : NoContraBrokers) : ∀ token ∈ entry.encode, token.tag ∈ NoContraBrokers.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoContraBrokers.shape] at this

theorem NoContraBrokers.led (entry : NoContraBrokers) : Lead [51, 55, 53] entry.encode :=
  lead_parts [51, 55, 53] entry.contraBroker _ NoContraBrokers.tags.tail rfl (by decide +kernel)

structure ExecutionReportExecutionReport where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  cumQty : Option (Terminated 1)  -- tag 14
  execID : Terminated 1  -- tag 17
  execTransType : Terminated 1  -- tag 20
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Terminated 1  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  leavesQty : Option (Terminated 1)  -- tag 151
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  tradeCondition : Option (Terminated 1)  -- tag 277
  noTradingSessions : List NoTradingSessions  -- tag 386
  noContraBrokers : List NoContraBrokers  -- tag 382
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  multilegReportingType : Terminated 1  -- tag 442
  optionalData : Option (Terminated 1)  -- tag 526
  legRefID : Option (Terminated 1)  -- tag 654
  selfTradeType : Option (Terminated 1)  -- tag 7928
  capStrategyID : Option (Terminated 1)  -- tag 7929
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  dealID : Option (Terminated 1)  -- tag 9483
  liquidityIndicator : Option (Terminated 1)  -- tag 9730
  flowIndicator : Terminated 1  -- tag 20005
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010
  contraCustomerOrFirm : Option (Terminated 1)  -- tag 20016
  contraClearingAccount : Option (Terminated 1)  -- tag 20017
  contraOpenClose : Option (Terminated 1)  -- tag 20018
  contraMarketMaker : Option (Terminated 1)  -- tag 20019
  allocationFirmMPID : Option (Terminated 1)  -- tag 20022
  allocationFirmMMID : Option (Terminated 1)  -- tag 20023
  allocationFirmIntroducingBadgeID : Option (Terminated 1)  -- tag 20024
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040
  refDealID : Option (Terminated 1)  -- tag 30002
  allocationIndicator : Option (Terminated 1)  -- tag 30003
  originalDealID : Option (Terminated 1)  -- tag 30006
  refExecTimestamp : Option (Terminated 1)  -- tag 30016

def ExecutionReportExecutionReport.parts (record : ExecutionReportExecutionReport) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.required [50, 48] record.execTransType,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.optional [50, 55, 55] record.tradeCondition,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.group [51, 56, 50] NoContraBrokers.members NoContraBrokers.encode NoContraBrokers.within record.noContraBrokers,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.required [52, 52, 50] record.multilegReportingType,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [55, 57, 50, 57] record.capStrategyID,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [57, 52, 56, 51] record.dealID,
   Part.optional [57, 55, 51, 48] record.liquidityIndicator,
   Part.required [50, 48, 48, 48, 53] record.flowIndicator,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime,
   Part.optional [50, 48, 48, 49, 54] record.contraCustomerOrFirm,
   Part.optional [50, 48, 48, 49, 55] record.contraClearingAccount,
   Part.optional [50, 48, 48, 49, 56] record.contraOpenClose,
   Part.optional [50, 48, 48, 49, 57] record.contraMarketMaker,
   Part.optional [50, 48, 48, 50, 50] record.allocationFirmMPID,
   Part.optional [50, 48, 48, 50, 51] record.allocationFirmMMID,
   Part.optional [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID,
   Part.optional [51, 48, 48, 48, 50] record.refDealID,
   Part.optional [51, 48, 48, 48, 51] record.allocationIndicator,
   Part.optional [51, 48, 48, 48, 54] record.originalDealID,
   Part.optional [51, 48, 48, 49, 54] record.refExecTimestamp]

def ExecutionReportExecutionReport.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 52]], [[49, 55]], [[50, 48]], [[51, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 53, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [[50, 55, 55]], [51, 56, 54] :: NoTradingSessions.members, [51, 56, 50] :: NoContraBrokers.members, [[52, 51, 57]], [[52, 52, 48]], [[52, 52, 50]], [[53, 50, 54]], [[54, 53, 52]], [[55, 57, 50, 56]], [[55, 57, 50, 57]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[57, 52, 56, 51]], [[57, 55, 51, 48]], [[50, 48, 48, 48, 53]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]], [[50, 48, 48, 49, 54]], [[50, 48, 48, 49, 55]], [[50, 48, 48, 49, 56]], [[50, 48, 48, 49, 57]], [[50, 48, 48, 50, 50]], [[50, 48, 48, 50, 51]], [[50, 48, 48, 50, 52]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]], [[51, 48, 48, 48, 50]], [[51, 48, 48, 48, 51]], [[51, 48, 48, 48, 54]], [[51, 48, 48, 49, 54]]]

theorem ExecutionReportExecutionReport.shape (record : ExecutionReportExecutionReport) : record.parts.map Part.tags = ExecutionReportExecutionReport.tags := rfl

def ExecutionReportExecutionReport.decode (tokens : List Token) : Option ExecutionReportExecutionReport := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let tradeCondition ← readOptional [50, 55, 55] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let noContraBrokers ← readGroup [51, 56, 50] [51, 55, 53] NoContraBrokers.members NoContraBrokers.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let multilegReportingType ← readRequired [52, 52, 50] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let capStrategyID ← readOptional [55, 57, 50, 57] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let dealID ← readOptional [57, 52, 56, 51] tokens
  let liquidityIndicator ← readOptional [57, 55, 51, 48] tokens
  let flowIndicator ← readRequired [50, 48, 48, 48, 53] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  let contraCustomerOrFirm ← readOptional [50, 48, 48, 49, 54] tokens
  let contraClearingAccount ← readOptional [50, 48, 48, 49, 55] tokens
  let contraOpenClose ← readOptional [50, 48, 48, 49, 56] tokens
  let contraMarketMaker ← readOptional [50, 48, 48, 49, 57] tokens
  let allocationFirmMPID ← readOptional [50, 48, 48, 50, 50] tokens
  let allocationFirmMMID ← readOptional [50, 48, 48, 50, 51] tokens
  let allocationFirmIntroducingBadgeID ← readOptional [50, 48, 48, 50, 52] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  let refDealID ← readOptional [51, 48, 48, 48, 50] tokens
  let allocationIndicator ← readOptional [51, 48, 48, 48, 51] tokens
  let originalDealID ← readOptional [51, 48, 48, 48, 54] tokens
  let refExecTimestamp ← readOptional [51, 48, 48, 49, 54] tokens
  pure { account, clOrdID, cumQty, execID, execTransType, lastMkt, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, tradeCondition, noTradingSessions, noContraBrokers, clearingFirm, clearingAccount, multilegReportingType, optionalData, legRefID, selfTradeType, capStrategyID, specialOrdType, extendedExecInst, introducingBadgeID, dealID, liquidityIndicator, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, contraCustomerOrFirm, contraClearingAccount, contraOpenClose, contraMarketMaker, allocationFirmMPID, allocationFirmMMID, allocationFirmIntroducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, refDealID, allocationIndicator, originalDealID, refExecTimestamp }

theorem ExecutionReportExecutionReport.decode_agrees (record : ExecutionReportExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReportExecutionReport.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have tradeCondition := readOptional_part [50, 55, 55] record.tradeCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have noContraBrokers := readGroup_part [51, 56, 50] [51, 55, 53] NoContraBrokers.members NoContraBrokers.encode NoContraBrokers.within NoContraBrokers.decode NoContraBrokers.decode_encode NoContraBrokers.led record.noContraBrokers tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have multilegReportingType := readRequired_part [52, 52, 50] record.multilegReportingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have capStrategyID := readOptional_part [55, 57, 50, 57] record.capStrategyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have dealID := readOptional_part [57, 52, 56, 51] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have liquidityIndicator := readOptional_part [57, 55, 51, 48] record.liquidityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have flowIndicator := readRequired_part [50, 48, 48, 48, 53] record.flowIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have contraCustomerOrFirm := readOptional_part [50, 48, 48, 49, 54] record.contraCustomerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have contraClearingAccount := readOptional_part [50, 48, 48, 49, 55] record.contraClearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have contraOpenClose := readOptional_part [50, 48, 48, 49, 56] record.contraOpenClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have contraMarketMaker := readOptional_part [50, 48, 48, 49, 57] record.contraMarketMaker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have allocationFirmMPID := readOptional_part [50, 48, 48, 50, 50] record.allocationFirmMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have allocationFirmMMID := readOptional_part [50, 48, 48, 50, 51] record.allocationFirmMMID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have allocationFirmIntroducingBadgeID := readOptional_part [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  have refDealID := readOptional_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 60 (by decide +kernel)))
  have allocationIndicator := readOptional_part [51, 48, 48, 48, 51] record.allocationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 61 (by decide +kernel)))
  have originalDealID := readOptional_part [51, 48, 48, 48, 54] record.originalDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 62 (by decide +kernel)))
  have refExecTimestamp := readOptional_part [51, 48, 48, 49, 54] record.refExecTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 63 (by decide +kernel)))
  simp only [ExecutionReportExecutionReport.decode, account, clOrdID, cumQty, execID, execTransType, lastMkt, lastPx, lastQty, orderID, orderQty, ordStatus, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, leavesQty, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, tradeCondition, noTradingSessions, noContraBrokers, clearingFirm, clearingAccount, multilegReportingType, optionalData, legRefID, selfTradeType, capStrategyID, specialOrdType, extendedExecInst, introducingBadgeID, dealID, liquidityIndicator, flowIndicator, nanosecondSendingTime, nanosecondTransactTime, contraCustomerOrFirm, contraClearingAccount, contraOpenClose, contraMarketMaker, allocationFirmMPID, allocationFirmMMID, allocationFirmIntroducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, refDealID, allocationIndicator, originalDealID, refExecTimestamp, some_bind] <;> rfl

theorem ExecutionReportExecutionReport.taken (record : ExecutionReportExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastMkt (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [50, 48, 52] record.customerOrFirm (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [50, 55, 55] record.tradeCondition (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_group pairing [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within (by decide) (by decide) NoTradingSessions.taken record.noTradingSessions)
                               (paired_cons pairing _ _ (paired_group pairing [51, 56, 50] NoContraBrokers.members NoContraBrokers.encode NoContraBrokers.within (by decide) (by decide) NoContraBrokers.taken record.noContraBrokers)
                                (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_required pairing [52, 52, 50] record.multilegReportingType (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [53, 50, 54] record.optionalData (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [54, 53, 52] record.legRefID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfTradeType (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 57] record.capStrategyID (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 50] record.specialOrdType (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_required pairing [57, 52, 49, 54] record.extendedExecInst (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_required pairing [57, 52, 52, 56] record.introducingBadgeID (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [57, 52, 56, 51] record.dealID (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [57, 55, 51, 48] record.liquidityIndicator (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 53] record.flowIndicator (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 54] record.contraCustomerOrFirm (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 55] record.contraClearingAccount (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 56] record.contraOpenClose (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 49, 57] record.contraMarketMaker (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 50] record.allocationFirmMPID (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 51] record.allocationFirmMMID (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID (by decide) (by decide))
                                                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 48] record.percentageStrike (by decide) (by decide))
                                                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 49] record.percentagePrice (by decide) (by decide))
                                                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 50] record.tiedHedgeIndicator (by decide) (by decide))
                                                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 53] record.tiedToStock (by decide) (by decide))
                                                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 55] record.refDelta (by decide) (by decide))
                                                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 56] record.stockPrice (by decide) (by decide))
                                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 51, 57] record.stockQty (by decide) (by decide))
                                                             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 52, 48] record.packageLinkID (by decide) (by decide))
                                                              (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 48, 50] record.refDealID (by decide) (by decide))
                                                               (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 48, 51] record.allocationIndicator (by decide) (by decide))
                                                                (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 48, 54] record.originalDealID (by decide) (by decide))
                                                                 (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 49, 54] record.refExecTimestamp (by decide) (by decide))
                                                                  (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

structure OrderCancelReject where
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  cxlRejResponseTo : Terminated 1  -- tag 434
  nanosecondSendingTime : Terminated 1  -- tag 20009
  nanosecondTransactTime : Terminated 1  -- tag 20010

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.required [52, 51, 52] record.cxlRejResponseTo,
   Part.required [50, 48, 48, 48, 57] record.nanosecondSendingTime,
   Part.required [50, 48, 48, 49, 48] record.nanosecondTransactTime]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[54, 48]], [[52, 51, 52]], [[50, 48, 48, 48, 57]], [[50, 48, 48, 49, 48]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  let nanosecondSendingTime ← readRequired [50, 48, 48, 48, 57] tokens
  let nanosecondTransactTime ← readRequired [50, 48, 48, 49, 48] tokens
  pure { clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejResponseTo, nanosecondSendingTime, nanosecondTransactTime }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have nanosecondSendingTime := readRequired_part [50, 48, 48, 48, 57] record.nanosecondSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have nanosecondTransactTime := readRequired_part [50, 48, 48, 49, 48] record.nanosecondTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [OrderCancelReject.decode, clOrdID, orderID, ordStatus, origClOrdID, text, transactTime, cxlRejResponseTo, nanosecondSendingTime, nanosecondTransactTime, some_bind] <;> rfl

theorem OrderCancelReject.taken (record : OrderCancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 48, 57] record.nanosecondSendingTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 48, 49, 48] record.nanosecondTransactTime (by decide) (by decide))
           (paired_none pairing)))))))))

inductive Message where
  | executionReportBrokerOpenOutcryAnnouncement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportBrokerOpenOutcryAnnouncement)
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired)
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired)
  | executionReportTradingOfficialOpenOutcryUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnapproval)
  | executionReportTradingOfficialOpenOutcryUnannoucement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannoucement)
  | executionReportTradingOfficialOpenOutcryUnannouncementUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval)
  | executionReportFLEXPriceRequest (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceRequest)
  | executionReportFLEXPriceReject (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceReject)
  | executionReportExecutionReport (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[78], [80], [81], [83], [87], [88], [85], [86]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)

def Message.tokens : Message → List Token
  | .executionReportBrokerOpenOutcryAnnouncement header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts)
  | .executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts)
  | .executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts)
  | .executionReportTradingOfficialOpenOutcryUnapproval header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts)
  | .executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts)
  | .executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts)
  | .executionReportFLEXPriceRequest header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts)
  | .executionReportFLEXPriceReject header r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts)
  | .executionReportExecutionReport header k0 r0 r1 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] k0.1] ++ r1.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if h0_0 : key.val = [78] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportBrokerOpenOutcryAnnouncement.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportBrokerOpenOutcryAnnouncement.decode rest
              pure (.executionReportBrokerOpenOutcryAnnouncement header r0 r1)
            else none
          else if h0_1 : key.val = [80] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode rest
              pure (.executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1)
            else none
          else if h0_2 : key.val = [81] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode rest
              pure (.executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1)
            else none
          else if h0_3 : key.val = [83] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradingOfficialOpenOutcryUnapproval.decode rest
              pure (.executionReportTradingOfficialOpenOutcryUnapproval header r0 r1)
            else none
          else if h0_4 : key.val = [87] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode rest
              pure (.executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1)
            else none
          else if h0_5 : key.val = [88] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode rest
              pure (.executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1)
            else none
          else if h0_6 : key.val = [85] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceRequest.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportFLEXPriceRequest.decode rest
              pure (.executionReportFLEXPriceRequest header r0 r1)
            else none
          else if h0_7 : key.val = [86] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceReject.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportFLEXPriceReject.decode rest
              pure (.executionReportFLEXPriceReject header r0 r1)
            else none
          else let k0 : {v : Terminated 1 // v.val ∉ ([[78], [80], [81], [83], [87], [88], [85], [86]] : List (List UInt8))} := ⟨key, by simp [h0_0, h0_1, h0_2, h0_3, h0_4, h0_5, h0_6, h0_7]⟩
          if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExecutionReport.tags) rest then do
            let header ← Header.decode rest
            let r0 ← ExecutionReport.decode rest
            let r1 ← ExecutionReportExecutionReport.decode rest
            pure (.executionReportExecutionReport header k0 r0 r1)
          else none
      else if token.value = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
        else none
      else none
    else none

theorem Message.decode_executionReportBrokerOpenOutcryAnnouncement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportBrokerOpenOutcryAnnouncement) :
    Message.decode (Message.tokens (.executionReportBrokerOpenOutcryAnnouncement header r0 r1)) = some (.executionReportBrokerOpenOutcryAnnouncement header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportBrokerOpenOutcryAnnouncement.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportBrokerOpenOutcryAnnouncement.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[78], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[78], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportBrokerOpenOutcryAnnouncement.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportBrokerOpenOutcryAnnouncement.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportBrokerOpenOutcryAnnouncement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportBrokerOpenOutcryAnnouncement.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) :
    Message.decode (Message.tokens (.executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[80], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) :
    Message.decode (Message.tokens (.executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[81], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[81], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradingOfficialOpenOutcryUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnapproval) :
    Message.decode (Message.tokens (.executionReportTradingOfficialOpenOutcryUnapproval header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnapproval header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[83], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[83], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradingOfficialOpenOutcryUnapproval.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnapproval.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradingOfficialOpenOutcryUnannoucement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannoucement) :
    Message.decode (Message.tokens (.executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[87], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[87], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradingOfficialOpenOutcryUnannoucement.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannoucement.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportTradingOfficialOpenOutcryUnannouncementUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) :
    Message.decode (Message.tokens (.executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[88], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[88], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportFLEXPriceRequest (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceRequest) :
    Message.decode (Message.tokens (.executionReportFLEXPriceRequest header r0 r1)) = some (.executionReportFLEXPriceRequest header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[85], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportFLEXPriceRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportFLEXPriceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportFLEXPriceReject (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceReject) :
    Message.decode (Message.tokens (.executionReportFLEXPriceReject header r0 r1)) = some (.executionReportFLEXPriceReject header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceReject.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportFLEXPriceReject.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[86], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[86], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportFLEXPriceReject.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportFLEXPriceReject.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportFLEXPriceReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportFLEXPriceReject.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportExecutionReport (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[78], [80], [81], [83], [87], [88], [85], [86]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportExecutionReport) :
    Message.decode (Message.tokens (.executionReportExecutionReport header k0 r0 r1)) = some (.executionReportExecutionReport header k0 r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] k0.1] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] k0.1] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportExecutionReport.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] k0.1]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportExecutionReport.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportExecutionReport.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] k0.1]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] k0.1] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportExecutionReport.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportBrokerOpenOutcryAnnouncement header r0 r1 => exact Message.decode_executionReportBrokerOpenOutcryAnnouncement header r0 r1
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1 => exact Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1 => exact Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1
  | executionReportTradingOfficialOpenOutcryUnapproval header r0 r1 => exact Message.decode_executionReportTradingOfficialOpenOutcryUnapproval header r0 r1
  | executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1 => exact Message.decode_executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1
  | executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1 => exact Message.decode_executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1
  | executionReportFLEXPriceRequest header r0 r1 => exact Message.decode_executionReportFLEXPriceRequest header r0 r1
  | executionReportFLEXPriceReject header r0 r1 => exact Message.decode_executionReportFLEXPriceReject header r0 r1
  | executionReportExecutionReport header k0 r0 r1 => exact Message.decode_executionReportExecutionReport header k0 r0 r1
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportBrokerOpenOutcryAnnouncement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportBrokerOpenOutcryAnnouncement) :
    Message.decodeBytes (Message.encode (.executionReportBrokerOpenOutcryAnnouncement header r0 r1)) = some (.executionReportBrokerOpenOutcryAnnouncement header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[78], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[78], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[78], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[78], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportBrokerOpenOutcryAnnouncement.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportBrokerOpenOutcryAnnouncement header r0 r1

theorem Message.decodeBytes_executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired) :
    Message.decodeBytes (Message.encode (.executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[80], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[80], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookrequired.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1

theorem Message.decodeBytes_executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired) :
    Message.decodeBytes (Message.encode (.executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[81], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[81], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[81], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[81], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1

theorem Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnapproval) :
    Message.decodeBytes (Message.encode (.executionReportTradingOfficialOpenOutcryUnapproval header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnapproval header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[83], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[83], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[83], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[83], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTradingOfficialOpenOutcryUnapproval.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradingOfficialOpenOutcryUnapproval header r0 r1

theorem Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnannoucement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannoucement) :
    Message.decodeBytes (Message.encode (.executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[87], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[87], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[87], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[87], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTradingOfficialOpenOutcryUnannoucement.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1

theorem Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnannouncementUnapproval (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval) :
    Message.decodeBytes (Message.encode (.executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1)) = some (.executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[88], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[88], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[88], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[88], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportTradingOfficialOpenOutcryUnannouncementUnapproval.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1

theorem Message.decodeBytes_executionReportFLEXPriceRequest (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceRequest) :
    Message.decodeBytes (Message.encode (.executionReportFLEXPriceRequest header r0 r1)) = some (.executionReportFLEXPriceRequest header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[85], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[85], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportFLEXPriceRequest.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFLEXPriceRequest header r0 r1

theorem Message.decodeBytes_executionReportFLEXPriceReject (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportFLEXPriceReject) :
    Message.decodeBytes (Message.encode (.executionReportFLEXPriceReject header r0 r1)) = some (.executionReportFLEXPriceReject header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] ⟨[86], by decide⟩] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[86], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[86], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[86], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportFLEXPriceReject.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportFLEXPriceReject header r0 r1

theorem Message.decodeBytes_executionReportExecutionReport (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[78], [80], [81], [83], [87], [88], [85], [86]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReportExecutionReport header k0 r0 r1)) = some (.executionReportExecutionReport header k0 r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] k0.1] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 53, 48] k0.1] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 53, 48] k0.1] ++ r1.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 53, 48] k0.1]) (r1.parts) (paired_cons pairing (Part.required [49, 53, 48] k0.1) [] (paired_required pairing [49, 53, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (ExecutionReportExecutionReport.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportExecutionReport header k0 r0 r1

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportBrokerOpenOutcryAnnouncement header r0 r1 => exact Message.decodeBytes_executionReportBrokerOpenOutcryAnnouncement header r0 r1
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1 => exact Message.decodeBytes_executionReportTradingOfficialOpenOutcryApprovalclearthebookrequired header r0 r1
  | executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1 => exact Message.decodeBytes_executionReportTradingOfficialOpenOutcryApprovalclearthebookNOTrequired header r0 r1
  | executionReportTradingOfficialOpenOutcryUnapproval header r0 r1 => exact Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnapproval header r0 r1
  | executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1 => exact Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnannoucement header r0 r1
  | executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1 => exact Message.decodeBytes_executionReportTradingOfficialOpenOutcryUnannouncementUnapproval header r0 r1
  | executionReportFLEXPriceRequest header r0 r1 => exact Message.decodeBytes_executionReportFLEXPriceRequest header r0 r1
  | executionReportFLEXPriceReject header r0 r1 => exact Message.decodeBytes_executionReportFLEXPriceReject header r0 r1
  | executionReportExecutionReport header k0 r0 r1 => exact Message.decodeBytes_executionReportExecutionReport header k0 r0 r1
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NyseArcaoptionsFloorbrokerFixV27Exchange
