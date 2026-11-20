import Wire

/-!
# Chicago Board Options Exchange Trade Reporting v1.55, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBxeequitiesTradereportingFixV155Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Option (Terminated 1)  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Option (Terminated 1)  -- tag 49
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128

def Header.parts (record : Header) : List Part :=
  [Part.optional [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 50, 50]], [[49, 50, 56]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readOptional [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, origSendingTime, deliverToCompID }

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
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, origSendingTime, deliverToCompID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 54] record.targetCompID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
           (paired_none pairing)))))))))

structure NoSides where
  side : Terminated 1  -- tag 54
  account : Option (Terminated 1)  -- tag 1
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452
  noPartyIDs : Option (Terminated 1)  -- tag 453
  partyID : Option (Terminated 1)  -- tag 448
  orderCapacity : Option (Terminated 1)  -- tag 528
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  centralCounterparty : Option (Terminated 1)  -- tag 7772
  feeCode : Option (Terminated 1)  -- tag 9882

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49] record.account,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole,
   Part.optional [52, 53, 51] record.noPartyIDs,
   Part.optional [52, 52, 56] record.partyID,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [55, 55, 55, 50] record.centralCounterparty,
   Part.optional [57, 56, 56, 50] record.feeCode]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49]], [[52, 52, 55]], [[52, 53, 50]], [[52, 53, 51]], [[52, 52, 56]], [[53, 50, 56]], [[54, 50, 53]], [[55, 55, 55, 50]], [[57, 56, 56, 50]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let account ← readOptional [49] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  let noPartyIDs ← readOptional [52, 53, 51] tokens
  let partyID ← readOptional [52, 52, 56] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let centralCounterparty ← readOptional [55, 55, 55, 50] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { side, account, partyIDSource, partyRole, noPartyIDs, partyID, orderCapacity, tradingSessionSubID, centralCounterparty, feeCode }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noPartyIDs := readOptional_part [52, 53, 51] record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyID := readOptional_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have centralCounterparty := readOptional_part [55, 55, 55, 50] record.centralCounterparty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoSides.decode, side, account, partyIDSource, partyRole, noPartyIDs, partyID, orderCapacity, tradingSessionSubID, centralCounterparty, feeCode, some_bind] <;> rfl

theorem NoSides.taken (record : NoSides) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 53, 50] record.partyRole (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 53, 51] record.noPartyIDs (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52, 56] record.partyID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 50, 53] record.tradingSessionSubID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 55, 55, 50] record.centralCounterparty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.feeCode (by decide) (by decide))
            (paired_none pairing))))))))))

def NoSides.members : List (List UInt8) := NoSides.tags.flatten

def NoSides.encode (entry : NoSides) : List Token := encodeParts entry.parts

theorem NoSides.decode_encode (entry : NoSides) : NoSides.decode entry.encode = some entry :=
  NoSides.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSides.within (entry : NoSides) : ∀ token ∈ entry.encode, token.tag ∈ NoSides.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSides.shape] at this

theorem NoSides.led (entry : NoSides) : Lead [53, 52] entry.encode :=
  lead_parts [53, 52] entry.side _ NoSides.tags.tail rfl (by decide +kernel)

structure TradeCaptureReportAck where
  currency : Option (Terminated 1)  -- tag 15
  iDSource : Option (Terminated 1)  -- tag 22
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  securityID : Option (Terminated 1)  -- tag 48
  symbol : Option (Terminated 1)  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Option (Terminated 1)  -- tag 150
  securityExchange : Option (Terminated 1)  -- tag 207
  grossTradeAmt : Option (Terminated 1)  -- tag 381
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  tradeReportID : Option (Terminated 1)  -- tag 571
  tradeReportRefID : Option (Terminated 1)  -- tag 572
  matchType : Option (Terminated 1)  -- tag 574
  trdType : Option (Terminated 1)  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  tradeReportType : Option (Terminated 1)  -- tag 856
  trdRptStatus : Option (Terminated 1)  -- tag 939
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Option (Terminated 1)  -- tag 1123
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  venueType : Option (Terminated 1)  -- tag 1430
  noTradePriceConditions : Option (Terminated 1)  -- tag 1838
  intraFirmTradeIndicator : Option (Terminated 1)  -- tag 2373
  execMethod : Option (Terminated 1)  -- tag 2405
  algorithmicTradeIndicator : Option (Terminated 1)  -- tag 2667
  tertiaryTrdType : Option (Terminated 1)  -- tag 2896
  multiJurisdictionReportingIndicator : Option (Terminated 1)  -- tag 2963
  trdRegPublicationReasons : Option (Terminated 1)  -- tag 8013
  noSides : List NoSides  -- tag 552
  origCompID : Option (Terminated 1)  -- tag 9688
  origSubID : Option (Terminated 1)  -- tag 9689

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [51, 56, 49] record.grossTradeAmt,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [53, 55, 49] record.tradeReportID,
   Part.optional [53, 55, 50] record.tradeReportRefID,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [57, 51, 57] record.trdRptStatus,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.optional [49, 56, 51, 56] record.noTradePriceConditions,
   Part.optional [50, 51, 55, 51] record.intraFirmTradeIndicator,
   Part.optional [50, 52, 48, 53] record.execMethod,
   Part.optional [50, 54, 54, 55] record.algorithmicTradeIndicator,
   Part.optional [50, 56, 57, 54] record.tertiaryTrdType,
   Part.optional [50, 57, 54, 51] record.multiJurisdictionReportingIndicator,
   Part.optional [56, 48, 49, 51] record.trdRegPublicationReasons,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [57, 54, 56, 56] record.origCompID,
   Part.optional [57, 54, 56, 57] record.origSubID]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[50, 50]], [[51, 48]], [[51, 49]], [[51, 50]], [[52, 56]], [[53, 53]], [[53, 56]], [[54, 48]], [[55, 53]], [[49, 53, 48]], [[50, 48, 55]], [[51, 56, 49]], [[52, 56, 55]], [[53, 55, 49]], [[53, 55, 50]], [[53, 55, 52]], [[56, 50, 56]], [[56, 50, 57]], [[56, 53, 53]], [[56, 53, 54]], [[57, 51, 57]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[49, 51, 57, 48]], [[49, 52, 51, 48]], [[49, 56, 51, 56]], [[50, 51, 55, 51]], [[50, 52, 48, 53]], [[50, 54, 54, 55]], [[50, 56, 57, 54]], [[50, 57, 54, 51]], [[56, 48, 49, 51]], [53, 53, 50] :: NoSides.members, [[57, 54, 56, 56]], [[57, 54, 56, 57]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let currency ← readOptional [49, 53] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let grossTradeAmt ← readOptional [51, 56, 49] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let tradeReportID ← readOptional [53, 55, 49] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let trdRptStatus ← readOptional [57, 51, 57] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readOptional [49, 49, 50, 51] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let noTradePriceConditions ← readOptional [49, 56, 51, 56] tokens
  let intraFirmTradeIndicator ← readOptional [50, 51, 55, 51] tokens
  let execMethod ← readOptional [50, 52, 48, 53] tokens
  let algorithmicTradeIndicator ← readOptional [50, 54, 54, 55] tokens
  let tertiaryTrdType ← readOptional [50, 56, 57, 54] tokens
  let multiJurisdictionReportingIndicator ← readOptional [50, 57, 54, 51] tokens
  let trdRegPublicationReasons ← readOptional [56, 48, 49, 51] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let origCompID ← readOptional [57, 54, 56, 56] tokens
  let origSubID ← readOptional [57, 54, 56, 57] tokens
  pure { currency, iDSource, lastMkt, lastPx, lastQty, securityID, symbol, text, transactTime, tradeDate, execType, securityExchange, grossTradeAmt, tradeReportTransType, tradeReportID, tradeReportRefID, matchType, trdType, trdSubType, secondaryTrdType, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, tradePublishIndicator, venueType, noTradePriceConditions, intraFirmTradeIndicator, execMethod, algorithmicTradeIndicator, tertiaryTrdType, multiJurisdictionReportingIndicator, trdRegPublicationReasons, noSides, origCompID, origSubID }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have grossTradeAmt := readOptional_part [51, 56, 49] record.grossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeReportID := readOptional_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have trdRptStatus := readOptional_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeHandlingInstr := readOptional_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noTradePriceConditions := readOptional_part [49, 56, 51, 56] record.noTradePriceConditions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have intraFirmTradeIndicator := readOptional_part [50, 51, 55, 51] record.intraFirmTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have execMethod := readOptional_part [50, 52, 48, 53] record.execMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have algorithmicTradeIndicator := readOptional_part [50, 54, 54, 55] record.algorithmicTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have tertiaryTrdType := readOptional_part [50, 56, 57, 54] record.tertiaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have multiJurisdictionReportingIndicator := readOptional_part [50, 57, 54, 51] record.multiJurisdictionReportingIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have trdRegPublicationReasons := readOptional_part [56, 48, 49, 51] record.trdRegPublicationReasons tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have origCompID := readOptional_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have origSubID := readOptional_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, currency, iDSource, lastMkt, lastPx, lastQty, securityID, symbol, text, transactTime, tradeDate, execType, securityExchange, grossTradeAmt, tradeReportTransType, tradeReportID, tradeReportRefID, matchType, trdType, trdSubType, secondaryTrdType, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, tradePublishIndicator, venueType, noTradePriceConditions, intraFirmTradeIndicator, execMethod, algorithmicTradeIndicator, tertiaryTrdType, multiJurisdictionReportingIndicator, trdRegPublicationReasons, noSides, origCompID, origSubID, some_bind] <;> rfl

theorem TradeCaptureReportAck.taken (record : TradeCaptureReportAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastMkt (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 56, 49] record.grossTradeAmt (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 56, 55] record.tradeReportTransType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 55, 49] record.tradeReportID (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 55, 50] record.tradeReportRefID (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [56, 50, 56] record.trdType (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [56, 50, 57] record.trdSubType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [56, 53, 53] record.secondaryTrdType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [56, 53, 54] record.tradeReportType (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [57, 51, 57] record.trdRptStatus (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 51] record.tradeID (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 51] record.tradeHandlingInstr (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 51, 57, 48] record.tradePublishIndicator (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 52, 51, 48] record.venueType (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 56, 51, 56] record.noTradePriceConditions (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [50, 51, 55, 51] record.intraFirmTradeIndicator (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [50, 52, 48, 53] record.execMethod (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 54, 54, 55] record.algorithmicTradeIndicator (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 56, 57, 54] record.tertiaryTrdType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 57, 54, 51] record.multiJurisdictionReportingIndicator (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 51] record.trdRegPublicationReasons (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSides.members NoSides.encode NoSides.within (by decide) (by decide) NoSides.taken record.noSides)
                                    (paired_cons pairing _ _ (paired_optional pairing [57, 54, 56, 56] record.origCompID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [57, 54, 56, 57] record.origSubID (by decide) (by decide))
                                      (paired_none pairing))))))))))))))))))))))))))))))))))))

structure TradeCaptureReport where
  currency : Option (Terminated 1)  -- tag 15
  iDSource : Option (Terminated 1)  -- tag 22
  lastMkt : Option (Terminated 1)  -- tag 30
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  securityID : Option (Terminated 1)  -- tag 48
  symbol : Option (Terminated 1)  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Option (Terminated 1)  -- tag 60
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Option (Terminated 1)  -- tag 150
  securityExchange : Option (Terminated 1)  -- tag 207
  contraBroker : Option (Terminated 1)  -- tag 375
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  tradeReportID : Option (Terminated 1)  -- tag 571
  tradeReportRefID : Option (Terminated 1)  -- tag 572
  matchStatus : Option (Terminated 1)  -- tag 573
  matchType : Option (Terminated 1)  -- tag 574
  trdType : Option (Terminated 1)  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  secondaryTrdType : Option (Terminated 1)  -- tag 855
  tradeReportType : Option (Terminated 1)  -- tag 856
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Option (Terminated 1)  -- tag 1123
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  venueType : Option (Terminated 1)  -- tag 1430
  noTradePriceConditions : Option (Terminated 1)  -- tag 1838
  intraFirmTradeIndicator : Option (Terminated 1)  -- tag 2373
  execMethod : Option (Terminated 1)  -- tag 2405
  algorithmicTradeIndicator : Option (Terminated 1)  -- tag 2667
  tertiaryTrdType : Option (Terminated 1)  -- tag 2896
  multiJurisdictionReportingIndicator : Option (Terminated 1)  -- tag 2963
  rptTime : Option (Terminated 1)  -- tag 7570
  trdRegPublicationReasons : Option (Terminated 1)  -- tag 8013
  noSides : List NoSides  -- tag 552

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.optional [49, 53] record.currency,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 48] record.lastMkt,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 48] record.transactTime,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.optional [53, 55, 49] record.tradeReportID,
   Part.optional [53, 55, 50] record.tradeReportRefID,
   Part.optional [53, 55, 51] record.matchStatus,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [56, 53, 53] record.secondaryTrdType,
   Part.optional [56, 53, 54] record.tradeReportType,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.optional [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.optional [49, 52, 51, 48] record.venueType,
   Part.optional [49, 56, 51, 56] record.noTradePriceConditions,
   Part.optional [50, 51, 55, 51] record.intraFirmTradeIndicator,
   Part.optional [50, 52, 48, 53] record.execMethod,
   Part.optional [50, 54, 54, 55] record.algorithmicTradeIndicator,
   Part.optional [50, 56, 57, 54] record.tertiaryTrdType,
   Part.optional [50, 57, 54, 51] record.multiJurisdictionReportingIndicator,
   Part.optional [55, 53, 55, 48] record.rptTime,
   Part.optional [56, 48, 49, 51] record.trdRegPublicationReasons,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[49, 53]], [[50, 50]], [[51, 48]], [[51, 49]], [[51, 50]], [[52, 56]], [[53, 53]], [[53, 56]], [[54, 48]], [[55, 53]], [[49, 53, 48]], [[50, 48, 55]], [[51, 55, 53]], [[52, 56, 55]], [[53, 55, 49]], [[53, 55, 50]], [[53, 55, 51]], [[53, 55, 52]], [[56, 50, 56]], [[56, 50, 57]], [[56, 53, 53]], [[56, 53, 54]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[49, 51, 57, 48]], [[49, 52, 51, 48]], [[49, 56, 51, 56]], [[50, 51, 55, 51]], [[50, 52, 48, 53]], [[50, 54, 54, 55]], [[50, 56, 57, 54]], [[50, 57, 54, 51]], [[55, 53, 55, 48]], [[56, 48, 49, 51]], [53, 53, 50] :: NoSides.members]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let currency ← readOptional [49, 53] tokens
  let iDSource ← readOptional [50, 50] tokens
  let lastMkt ← readOptional [51, 48] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readOptional [54, 48] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let tradeReportID ← readOptional [53, 55, 49] tokens
  let tradeReportRefID ← readOptional [53, 55, 50] tokens
  let matchStatus ← readOptional [53, 55, 51] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let secondaryTrdType ← readOptional [56, 53, 53] tokens
  let tradeReportType ← readOptional [56, 53, 54] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readOptional [49, 49, 50, 51] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let venueType ← readOptional [49, 52, 51, 48] tokens
  let noTradePriceConditions ← readOptional [49, 56, 51, 56] tokens
  let intraFirmTradeIndicator ← readOptional [50, 51, 55, 51] tokens
  let execMethod ← readOptional [50, 52, 48, 53] tokens
  let algorithmicTradeIndicator ← readOptional [50, 54, 54, 55] tokens
  let tertiaryTrdType ← readOptional [50, 56, 57, 54] tokens
  let multiJurisdictionReportingIndicator ← readOptional [50, 57, 54, 51] tokens
  let rptTime ← readOptional [55, 53, 55, 48] tokens
  let trdRegPublicationReasons ← readOptional [56, 48, 49, 51] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  pure { currency, iDSource, lastMkt, lastPx, lastQty, securityID, symbol, text, transactTime, tradeDate, execType, securityExchange, contraBroker, tradeReportTransType, tradeReportID, tradeReportRefID, matchStatus, matchType, trdType, trdSubType, secondaryTrdType, tradeReportType, tradeID, tradeHandlingInstr, tradePublishIndicator, venueType, noTradePriceConditions, intraFirmTradeIndicator, execMethod, algorithmicTradeIndicator, tertiaryTrdType, multiJurisdictionReportingIndicator, rptTime, trdRegPublicationReasons, noSides }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastMkt := readOptional_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeReportID := readOptional_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have tradeReportRefID := readOptional_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have matchStatus := readOptional_part [53, 55, 51] record.matchStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have secondaryTrdType := readOptional_part [56, 53, 53] record.secondaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tradeReportType := readOptional_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeHandlingInstr := readOptional_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have venueType := readOptional_part [49, 52, 51, 48] record.venueType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noTradePriceConditions := readOptional_part [49, 56, 51, 56] record.noTradePriceConditions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have intraFirmTradeIndicator := readOptional_part [50, 51, 55, 51] record.intraFirmTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have execMethod := readOptional_part [50, 52, 48, 53] record.execMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have algorithmicTradeIndicator := readOptional_part [50, 54, 54, 55] record.algorithmicTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have tertiaryTrdType := readOptional_part [50, 56, 57, 54] record.tertiaryTrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have multiJurisdictionReportingIndicator := readOptional_part [50, 57, 54, 51] record.multiJurisdictionReportingIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have rptTime := readOptional_part [55, 53, 55, 48] record.rptTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have trdRegPublicationReasons := readOptional_part [56, 48, 49, 51] record.trdRegPublicationReasons tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, currency, iDSource, lastMkt, lastPx, lastQty, securityID, symbol, text, transactTime, tradeDate, execType, securityExchange, contraBroker, tradeReportTransType, tradeReportID, tradeReportRefID, matchStatus, matchType, trdType, trdSubType, secondaryTrdType, tradeReportType, tradeID, tradeHandlingInstr, tradePublishIndicator, venueType, noTradePriceConditions, intraFirmTradeIndicator, execMethod, algorithmicTradeIndicator, tertiaryTrdType, multiJurisdictionReportingIndicator, rptTime, trdRegPublicationReasons, noSides, some_bind] <;> rfl

theorem TradeCaptureReport.taken (record : TradeCaptureReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 48] record.lastMkt (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 56, 55] record.tradeReportTransType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 55, 49] record.tradeReportID (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 55, 50] record.tradeReportRefID (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [53, 55, 51] record.matchStatus (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [56, 50, 56] record.trdType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [56, 50, 57] record.trdSubType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [56, 53, 53] record.secondaryTrdType (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [56, 53, 54] record.tradeReportType (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 51] record.tradeID (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 51] record.tradeHandlingInstr (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 51, 57, 48] record.tradePublishIndicator (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 52, 51, 48] record.venueType (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 56, 51, 56] record.noTradePriceConditions (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [50, 51, 55, 51] record.intraFirmTradeIndicator (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [50, 52, 48, 53] record.execMethod (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 54, 54, 55] record.algorithmicTradeIndicator (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 56, 57, 54] record.tertiaryTrdType (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 57, 54, 51] record.multiJurisdictionReportingIndicator (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [55, 53, 55, 48] record.rptTime (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [56, 48, 49, 51] record.trdRegPublicationReasons (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSides.members NoSides.encode NoSides.within (by decide) (by decide) NoSides.taken record.noSides)
                                     (paired_none pairing)))))))))))))))))))))))))))))))))))

structure QuoteStatusReport where
  quoteID : Option (Terminated 1)  -- tag 117
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  securityExchange : Option (Terminated 1)  -- tag 207
  currency : Option (Terminated 1)  -- tag 15
  bidPx : Option (Terminated 1)  -- tag 132
  offerPx : Option (Terminated 1)  -- tag 133
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135
  quoteStatus : Option (Terminated 1)  -- tag 297
  text : Option (Terminated 1)  -- tag 58

def QuoteStatusReport.parts (record : QuoteStatusReport) : List Part :=
  [Part.optional [49, 49, 55] record.quoteID,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [50, 57, 55] record.quoteStatus,
   Part.optional [53, 56] record.text]

def QuoteStatusReport.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[53, 53]], [[52, 56]], [[50, 50]], [[50, 48, 55]], [[49, 53]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]], [[50, 57, 55]], [[53, 56]]]

theorem QuoteStatusReport.shape (record : QuoteStatusReport) : record.parts.map Part.tags = QuoteStatusReport.tags := rfl

def QuoteStatusReport.decode (tokens : List Token) : Option QuoteStatusReport := do
  let quoteID ← readOptional [49, 49, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let quoteStatus ← readOptional [50, 57, 55] tokens
  let text ← readOptional [53, 56] tokens
  pure { quoteID, symbol, securityID, iDSource, securityExchange, currency, bidPx, offerPx, bidSize, offerSize, quoteStatus, text }

theorem QuoteStatusReport.decode_agrees (record : QuoteStatusReport) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteStatusReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteStatusReport.decode tokens = some record := by
  have distinct : QuoteStatusReport.tags.flatten.Nodup := by decide +kernel
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have quoteStatus := readOptional_part [50, 57, 55] record.quoteStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [QuoteStatusReport.decode, quoteID, symbol, securityID, iDSource, securityExchange, currency, bidPx, offerPx, bidSize, offerSize, quoteStatus, text, some_bind] <;> rfl

theorem QuoteStatusReport.taken (record : QuoteStatusReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.iDSource (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50] record.bidPx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 51, 51] record.offerPx (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 51, 52] record.bidSize (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 51, 53] record.offerSize (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 57, 55] record.quoteStatus (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
              (paired_none pairing))))))))))))

inductive Message where
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | quoteStatusReport (header : Header) (r0 : QuoteStatusReport)

def Message.tokens : Message → List Token
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], [65, 82]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], [65, 69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteStatusReport header r0 => ⟨[51, 53], [65, 73]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [65, 82] then
        if known (Header.tags ++ TradeCaptureReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportAck.decode rest
          pure (.tradeCaptureReportAck header r0)
        else none
      else if token.value = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value = [65, 73] then
        if known (Header.tags ++ QuoteStatusReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteStatusReport.decode rest
          pure (.quoteStatusReport header r0)
        else none
      else none
    else none

theorem Message.decode_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decode (Message.tokens (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decode (Message.tokens (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteStatusReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteStatusReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteStatusReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | quoteStatusReport header r0 => exact Message.decode_quoteStatusReport header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 82]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReportAck.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_quoteStatusReport (header : Header) (r0 : QuoteStatusReport) :
    Message.decodeBytes (Message.encode (.quoteStatusReport header r0)) = some (.quoteStatusReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 73]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteStatusReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteStatusReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | quoteStatusReport header r0 => exact Message.decodeBytes_quoteStatusReport header r0

/-- BeginString as the venue states it: one of FIX.4.2, FIX.4.4, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 50], [70, 73, 88, 46, 52, 46, 52]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.CboeBxeequitiesTradereportingFixV155Exchange
