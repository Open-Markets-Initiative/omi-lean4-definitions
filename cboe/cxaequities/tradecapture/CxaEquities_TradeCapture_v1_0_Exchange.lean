import Wire

/-!
# Chicago Board Options Exchange Trade Capture v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCxaequitiesTradecaptureFixV10Exchange

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

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, some_bind] <;> rfl

def NoPartyIDs.members : List (List UInt8) := NoPartyIDs.tags.flatten

def NoPartyIDs.encode (entry : NoPartyIDs) : List Token := encodeParts entry.parts

theorem NoPartyIDs.decode_encode (entry : NoPartyIDs) : NoPartyIDs.decode entry.encode = some entry :=
  NoPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyIDs.within (entry : NoPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyIDs.shape] at this

theorem NoPartyIDs.led (entry : NoPartyIDs) : Lead [52, 52, 56] entry.encode :=
  lead_parts [52, 52, 56] entry.partyID _ NoPartyIDs.tags.tail rfl (by decide +kernel)

structure NoSides where
  side : Terminated 1  -- tag 54
  clOrdId : Option (Terminated 1)  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  account : Option (Terminated 1)  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 47
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  noPartyIDs : List NoPartyIDs  -- tag 453
  clientCrossRef : Option (Terminated 1)  -- tag 6802
  shortSellNakedQty : Option (Terminated 1)  -- tag 6803
  shortSellCoveredQty : Option (Terminated 1)  -- tag 6804
  shortSellLongQty : Option (Terminated 1)  -- tag 6805
  originOfTrans : Option (Terminated 1)  -- tag 8138
  intermediaryID : Option (Terminated 1)  -- tag 8139
  directedWholesaleIndic : Option (Terminated 1)  -- tag 8140
  feeCode : Option (Terminated 1)  -- tag 9882

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49, 49] record.clOrdId,
   Part.optional [51, 55] record.orderID,
   Part.optional [49] record.account,
   Part.optional [52, 55] record.orderCapacity,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [54, 56, 48, 50] record.clientCrossRef,
   Part.optional [54, 56, 48, 51] record.shortSellNakedQty,
   Part.optional [54, 56, 48, 52] record.shortSellCoveredQty,
   Part.optional [54, 56, 48, 53] record.shortSellLongQty,
   Part.optional [56, 49, 51, 56] record.originOfTrans,
   Part.optional [56, 49, 51, 57] record.intermediaryID,
   Part.optional [56, 49, 52, 48] record.directedWholesaleIndic,
   Part.optional [57, 56, 56, 50] record.feeCode]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 49]], [[51, 55]], [[49]], [[52, 55]], [[52, 51, 57]], [[52, 52, 48]], [52, 53, 51] :: NoPartyIDs.members, [[54, 56, 48, 50]], [[54, 56, 48, 51]], [[54, 56, 48, 52]], [[54, 56, 48, 53]], [[56, 49, 51, 56]], [[56, 49, 51, 57]], [[56, 49, 52, 48]], [[57, 56, 56, 50]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let clOrdId ← readOptional [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let account ← readOptional [49] tokens
  let orderCapacity ← readOptional [52, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let clientCrossRef ← readOptional [54, 56, 48, 50] tokens
  let shortSellNakedQty ← readOptional [54, 56, 48, 51] tokens
  let shortSellCoveredQty ← readOptional [54, 56, 48, 52] tokens
  let shortSellLongQty ← readOptional [54, 56, 48, 53] tokens
  let originOfTrans ← readOptional [56, 49, 51, 56] tokens
  let intermediaryID ← readOptional [56, 49, 51, 57] tokens
  let directedWholesaleIndic ← readOptional [56, 49, 52, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { side, clOrdId, orderID, account, orderCapacity, clearingFirm, clearingAccount, noPartyIDs, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, originOfTrans, intermediaryID, directedWholesaleIndic, feeCode }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readOptional_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderCapacity := readOptional_part [52, 55] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clientCrossRef := readOptional_part [54, 56, 48, 50] record.clientCrossRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have shortSellNakedQty := readOptional_part [54, 56, 48, 51] record.shortSellNakedQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have shortSellCoveredQty := readOptional_part [54, 56, 48, 52] record.shortSellCoveredQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have shortSellLongQty := readOptional_part [54, 56, 48, 53] record.shortSellLongQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have originOfTrans := readOptional_part [56, 49, 51, 56] record.originOfTrans tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have intermediaryID := readOptional_part [56, 49, 51, 57] record.intermediaryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have directedWholesaleIndic := readOptional_part [56, 49, 52, 48] record.directedWholesaleIndic tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [NoSides.decode, side, clOrdId, orderID, account, orderCapacity, clearingFirm, clearingAccount, noPartyIDs, clientCrossRef, shortSellNakedQty, shortSellCoveredQty, shortSellLongQty, originOfTrans, intermediaryID, directedWholesaleIndic, feeCode, some_bind] <;> rfl

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
  possResend : Option (Terminated 1)  -- tag 97
  transactTime : Terminated 1  -- tag 60
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  symbol : Terminated 1  -- tag 55
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Terminated 1  -- tag 150
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  noSides : List NoSides  -- tag 552
  tradeReportID : Terminated 1  -- tag 571
  tradeLinkID : Option (Terminated 1)  -- tag 820
  tradeReportType : Terminated 1  -- tag 856
  trdRptStatus : Terminated 1  -- tag 939
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Terminated 1  -- tag 1123
  execVenue : Option (Terminated 1)  -- tag 4805
  t1Settlement : Option (Terminated 1)  -- tag 8080
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  offExchTradeReportType : Terminated 1  -- tag 8181

def TradeCaptureReportAck.parts (record : TradeCaptureReportAck) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [53, 53] record.symbol,
   Part.optional [55, 53] record.tradeDate,
   Part.required [49, 53, 48] record.execType,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [56, 50, 48] record.tradeLinkID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.required [57, 51, 57] record.trdRptStatus,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [52, 56, 48, 53] record.execVenue,
   Part.optional [56, 48, 56, 48] record.t1Settlement,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.required [56, 49, 56, 49] record.offExchTradeReportType]

def TradeCaptureReportAck.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[54, 48]], [[51, 49]], [[51, 50]], [[53, 53]], [[55, 53]], [[49, 53, 48]], [[52, 56, 55]], [53, 53, 50] :: NoSides.members, [[53, 55, 49]], [[56, 50, 48]], [[56, 53, 54]], [[57, 51, 57]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[52, 56, 48, 53]], [[56, 48, 56, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 49]]]

theorem TradeCaptureReportAck.shape (record : TradeCaptureReportAck) : record.parts.map Part.tags = TradeCaptureReportAck.tags := rfl

def TradeCaptureReportAck.decode (tokens : List Token) : Option TradeCaptureReportAck := do
  let possResend ← readOptional [57, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeLinkID ← readOptional [56, 50, 48] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let trdRptStatus ← readRequired [57, 51, 57] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let execVenue ← readOptional [52, 56, 48, 53] tokens
  let t1Settlement ← readOptional [56, 48, 56, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let offExchTradeReportType ← readRequired [56, 49, 56, 49] tokens
  pure { possResend, transactTime, lastPx, lastShares, symbol, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeLinkID, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, execVenue, t1Settlement, removeCrossingFromClearing, offExchTradeReportType }

theorem TradeCaptureReportAck.decode_agrees (record : TradeCaptureReportAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportAck.decode tokens = some record := by
  have distinct : TradeCaptureReportAck.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeLinkID := readOptional_part [56, 50, 48] record.tradeLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have trdRptStatus := readRequired_part [57, 51, 57] record.trdRptStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execVenue := readOptional_part [52, 56, 48, 53] record.execVenue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have t1Settlement := readOptional_part [56, 48, 56, 48] record.t1Settlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have offExchTradeReportType := readRequired_part [56, 49, 56, 49] record.offExchTradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  simp only [TradeCaptureReportAck.decode, possResend, transactTime, lastPx, lastShares, symbol, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeLinkID, tradeReportType, trdRptStatus, tradeID, tradeHandlingInstr, execVenue, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, some_bind] <;> rfl

structure TradeCaptureReport where
  possResend : Option (Terminated 1)  -- tag 97
  transactTime : Terminated 1  -- tag 60
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  settlmntTyp : Option (Terminated 1)  -- tag 63
  futSettDate : Option (Terminated 1)  -- tag 64
  tradeDate : Option (Terminated 1)  -- tag 75
  execType : Terminated 1  -- tag 150
  tradeReportTransType : Option (Terminated 1)  -- tag 487
  noSides : List NoSides  -- tag 552
  tradeReportID : Terminated 1  -- tag 571
  tradeReportRefID : Terminated 1  -- tag 572
  tradeLinkID : Option (Terminated 1)  -- tag 820
  tradeReportType : Terminated 1  -- tag 856
  tradeID : Option (Terminated 1)  -- tag 1003
  tradeHandlingInstr : Terminated 1  -- tag 1123
  execVenue : Option (Terminated 1)  -- tag 4805
  transactID : Terminated 1  -- tag 6807
  t1Settlement : Option (Terminated 1)  -- tag 8080
  removeCrossingFromClearing : Option (Terminated 1)  -- tag 8177
  offExchTradeReportType : Terminated 1  -- tag 8181
  origCompID : Terminated 1  -- tag 9688
  origSubID : Terminated 1  -- tag 9689

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.required [54, 48] record.transactTime,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 52] record.futSettDate,
   Part.optional [55, 53] record.tradeDate,
   Part.required [49, 53, 48] record.execType,
   Part.optional [52, 56, 55] record.tradeReportTransType,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.required [53, 55, 50] record.tradeReportRefID,
   Part.optional [56, 50, 48] record.tradeLinkID,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.optional [49, 48, 48, 51] record.tradeID,
   Part.required [49, 49, 50, 51] record.tradeHandlingInstr,
   Part.optional [52, 56, 48, 53] record.execVenue,
   Part.required [54, 56, 48, 55] record.transactID,
   Part.optional [56, 48, 56, 48] record.t1Settlement,
   Part.optional [56, 49, 55, 55] record.removeCrossingFromClearing,
   Part.required [56, 49, 56, 49] record.offExchTradeReportType,
   Part.required [57, 54, 56, 56] record.origCompID,
   Part.required [57, 54, 56, 57] record.origSubID]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[54, 48]], [[51, 49]], [[51, 50]], [[53, 53]], [[53, 56]], [[54, 51]], [[54, 52]], [[55, 53]], [[49, 53, 48]], [[52, 56, 55]], [53, 53, 50] :: NoSides.members, [[53, 55, 49]], [[53, 55, 50]], [[56, 50, 48]], [[56, 53, 54]], [[49, 48, 48, 51]], [[49, 49, 50, 51]], [[52, 56, 48, 53]], [[54, 56, 48, 55]], [[56, 48, 56, 48]], [[56, 49, 55, 55]], [[56, 49, 56, 49]], [[57, 54, 56, 56]], [[57, 54, 56, 57]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let possResend ← readOptional [57, 55] tokens
  let transactTime ← readRequired [54, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let futSettDate ← readOptional [54, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let tradeReportTransType ← readOptional [52, 56, 55] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let tradeReportRefID ← readRequired [53, 55, 50] tokens
  let tradeLinkID ← readOptional [56, 50, 48] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let tradeID ← readOptional [49, 48, 48, 51] tokens
  let tradeHandlingInstr ← readRequired [49, 49, 50, 51] tokens
  let execVenue ← readOptional [52, 56, 48, 53] tokens
  let transactID ← readRequired [54, 56, 48, 55] tokens
  let t1Settlement ← readOptional [56, 48, 56, 48] tokens
  let removeCrossingFromClearing ← readOptional [56, 49, 55, 55] tokens
  let offExchTradeReportType ← readRequired [56, 49, 56, 49] tokens
  let origCompID ← readRequired [57, 54, 56, 56] tokens
  let origSubID ← readRequired [57, 54, 56, 57] tokens
  pure { possResend, transactTime, lastPx, lastShares, symbol, text, settlmntTyp, futSettDate, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeReportRefID, tradeLinkID, tradeReportType, tradeID, tradeHandlingInstr, execVenue, transactID, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, origCompID, origSubID }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have futSettDate := readOptional_part [54, 52] record.futSettDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeReportTransType := readOptional_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have tradeReportRefID := readRequired_part [53, 55, 50] record.tradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have tradeLinkID := readOptional_part [56, 50, 48] record.tradeLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradeID := readOptional_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have tradeHandlingInstr := readRequired_part [49, 49, 50, 51] record.tradeHandlingInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have execVenue := readOptional_part [52, 56, 48, 53] record.execVenue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have transactID := readRequired_part [54, 56, 48, 55] record.transactID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have t1Settlement := readOptional_part [56, 48, 56, 48] record.t1Settlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have removeCrossingFromClearing := readOptional_part [56, 49, 55, 55] record.removeCrossingFromClearing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have offExchTradeReportType := readRequired_part [56, 49, 56, 49] record.offExchTradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have origCompID := readRequired_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have origSubID := readRequired_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, possResend, transactTime, lastPx, lastShares, symbol, text, settlmntTyp, futSettDate, tradeDate, execType, tradeReportTransType, noSides, tradeReportID, tradeReportRefID, tradeLinkID, tradeReportType, tradeID, tradeHandlingInstr, execVenue, transactID, t1Settlement, removeCrossingFromClearing, offExchTradeReportType, origCompID, origSubID, some_bind] <;> rfl

inductive Message where
  | tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)

def Message.tokens : Message → List Token
  | .tradeCaptureReportAck header r0 => ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [65, 82] then
        if known (Header.tags ++ TradeCaptureReportAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportAck.decode rest
          pure (.tradeCaptureReportAck header r0)
        else none
      else if token.value.val = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | tradeCaptureReportAck header r0 => exact Message.decode_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_tradeCaptureReportAck (header : Header) (r0 : TradeCaptureReportAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportAck header r0)) = some (.tradeCaptureReportAck header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 82], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportAck.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportAck header r0

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 69], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | tradeCaptureReportAck header r0 => exact Message.decodeBytes_tradeCaptureReportAck header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCxaequitiesTradecaptureFixV10Exchange
