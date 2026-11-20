import Wire

/-!
# Chicago Board Options Exchange Order Entry v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeMatchnowOrderentryFixV10Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompId : Terminated 1  -- tag 115

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.required [49, 49, 53] record.onBehalfOfCompId]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[53, 50]], [[49, 50, 50]], [[49, 49, 53]]]

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
  let onBehalfOfCompId ← readRequired [49, 49, 53] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId }

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
  have onBehalfOfCompId := readRequired_part [49, 49, 53] record.onBehalfOfCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 48] record.senderSubID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 55] record.targetSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 49, 53] record.onBehalfOfCompId (by decide) (by decide))
           (paired_none pairing)))))))))

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

structure ExecutionReportCross where
  execTransType : Terminated 1  -- tag 20
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdId : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  currency : Terminated 1  -- tag 15
  execID : Terminated 1  -- tag 17
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  settlmntTyp : Option (Terminated 1)  -- tag 63
  futSettDate : Option (Terminated 1)  -- tag 64
  ordRejReason : Option (Terminated 1)  -- tag 103
  leavesQty : Terminated 1  -- tag 151
  lEIOrderOrigination : Option (Terminated 1)  -- tag 1724
  lEIRoutingArrangementIndicator : Option (Terminated 1)  -- tag 2883
  uMIRAccountType : Terminated 1  -- tag 6750
  uMIRUserID : Terminated 1  -- tag 6751
  basketTrade : Option (Terminated 1)  -- tag 6754
  programTrade : Option (Terminated 1)  -- tag 6755
  jitney : Option (Terminated 1)  -- tag 6757
  anonymous : Option (Terminated 1)  -- tag 6761
  uMIRRegulationID : Option (Terminated 1)  -- tag 6763
  crossType : Option (Terminated 1)  -- tag 6773
  principalTrade : Option (Terminated 1)  -- tag 6776
  nonResident : Option (Terminated 1)  -- tag 6783
  byPass : Option (Terminated 1)  -- tag 6791
  nCIB : Option (Terminated 1)  -- tag 6792
  shortMarkingExempt : Option (Terminated 1)  -- tag 7729
  lEICustomerAccount : Option (Terminated 1)  -- tag 8025
  lEIAlgorithmID : Option (Terminated 1)  -- tag 8026
  customerLEI : Option (Terminated 1)  -- tag 8027
  brokerLEI : Option (Terminated 1)  -- tag 8028
  feeCode : Option (Terminated 1)  -- tag 9882

def ExecutionReportCross.parts (record : ExecutionReportCross) : List Part :=
  [Part.required [50, 48] record.execTransType,
   Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdId,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 53] record.currency,
   Part.required [49, 55] record.execID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 52] record.futSettDate,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [49, 55, 50, 52] record.lEIOrderOrigination,
   Part.optional [50, 56, 56, 51] record.lEIRoutingArrangementIndicator,
   Part.required [54, 55, 53, 48] record.uMIRAccountType,
   Part.required [54, 55, 53, 49] record.uMIRUserID,
   Part.optional [54, 55, 53, 52] record.basketTrade,
   Part.optional [54, 55, 53, 53] record.programTrade,
   Part.optional [54, 55, 53, 55] record.jitney,
   Part.optional [54, 55, 54, 49] record.anonymous,
   Part.optional [54, 55, 54, 51] record.uMIRRegulationID,
   Part.optional [54, 55, 55, 51] record.crossType,
   Part.optional [54, 55, 55, 54] record.principalTrade,
   Part.optional [54, 55, 56, 51] record.nonResident,
   Part.optional [54, 55, 57, 49] record.byPass,
   Part.optional [54, 55, 57, 50] record.nCIB,
   Part.optional [55, 55, 50, 57] record.shortMarkingExempt,
   Part.optional [56, 48, 50, 53] record.lEICustomerAccount,
   Part.optional [56, 48, 50, 54] record.lEIAlgorithmID,
   Part.optional [56, 48, 50, 55] record.customerLEI,
   Part.optional [56, 48, 50, 56] record.brokerLEI,
   Part.optional [57, 56, 56, 50] record.feeCode]

def ExecutionReportCross.tags : List (List (List UInt8)) :=
  [[[50, 48]], [[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 53]], [[49, 55]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[54, 48]], [[54, 51]], [[54, 52]], [[49, 48, 51]], [[49, 53, 49]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 53, 48]], [[54, 55, 53, 49]], [[54, 55, 53, 52]], [[54, 55, 53, 53]], [[54, 55, 53, 55]], [[54, 55, 54, 49]], [[54, 55, 54, 51]], [[54, 55, 55, 51]], [[54, 55, 55, 54]], [[54, 55, 56, 51]], [[54, 55, 57, 49]], [[54, 55, 57, 50]], [[55, 55, 50, 57]], [[56, 48, 50, 53]], [[56, 48, 50, 54]], [[56, 48, 50, 55]], [[56, 48, 50, 56]], [[57, 56, 56, 50]]]

theorem ExecutionReportCross.shape (record : ExecutionReportCross) : record.parts.map Part.tags = ExecutionReportCross.tags := rfl

def ExecutionReportCross.decode (tokens : List Token) : Option ExecutionReportCross := do
  let execTransType ← readRequired [50, 48] tokens
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let currency ← readRequired [49, 53] tokens
  let execID ← readRequired [49, 55] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let futSettDate ← readOptional [54, 52] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let lEIOrderOrigination ← readOptional [49, 55, 50, 52] tokens
  let lEIRoutingArrangementIndicator ← readOptional [50, 56, 56, 51] tokens
  let uMIRAccountType ← readRequired [54, 55, 53, 48] tokens
  let uMIRUserID ← readRequired [54, 55, 53, 49] tokens
  let basketTrade ← readOptional [54, 55, 53, 52] tokens
  let programTrade ← readOptional [54, 55, 53, 53] tokens
  let jitney ← readOptional [54, 55, 53, 55] tokens
  let anonymous ← readOptional [54, 55, 54, 49] tokens
  let uMIRRegulationID ← readOptional [54, 55, 54, 51] tokens
  let crossType ← readOptional [54, 55, 55, 51] tokens
  let principalTrade ← readOptional [54, 55, 55, 54] tokens
  let nonResident ← readOptional [54, 55, 56, 51] tokens
  let byPass ← readOptional [54, 55, 57, 49] tokens
  let nCIB ← readOptional [54, 55, 57, 50] tokens
  let shortMarkingExempt ← readOptional [55, 55, 50, 57] tokens
  let lEICustomerAccount ← readOptional [56, 48, 50, 53] tokens
  let lEIAlgorithmID ← readOptional [56, 48, 50, 54] tokens
  let customerLEI ← readOptional [56, 48, 50, 55] tokens
  let brokerLEI ← readOptional [56, 48, 50, 56] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { execTransType, account, avgPx, clOrdId, cumQty, currency, execID, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, transactTime, settlmntTyp, futSettDate, ordRejReason, leavesQty, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, crossType, principalTrade, nonResident, byPass, nCIB, shortMarkingExempt, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, feeCode }

theorem ExecutionReportCross.decode_agrees (record : ExecutionReportCross) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCross.decode tokens = some record := by
  have distinct : ExecutionReportCross.tags.flatten.Nodup := by decide +kernel
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have futSettDate := readOptional_part [54, 52] record.futSettDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have lEIOrderOrigination := readOptional_part [49, 55, 50, 52] record.lEIOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lEIRoutingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.lEIRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have uMIRAccountType := readRequired_part [54, 55, 53, 48] record.uMIRAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have uMIRUserID := readRequired_part [54, 55, 53, 49] record.uMIRUserID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have basketTrade := readOptional_part [54, 55, 53, 52] record.basketTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have programTrade := readOptional_part [54, 55, 53, 53] record.programTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have jitney := readOptional_part [54, 55, 53, 55] record.jitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have anonymous := readOptional_part [54, 55, 54, 49] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have crossType := readOptional_part [54, 55, 55, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have principalTrade := readOptional_part [54, 55, 55, 54] record.principalTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have nonResident := readOptional_part [54, 55, 56, 51] record.nonResident tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have byPass := readOptional_part [54, 55, 57, 49] record.byPass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have nCIB := readOptional_part [54, 55, 57, 50] record.nCIB tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have shortMarkingExempt := readOptional_part [55, 55, 50, 57] record.shortMarkingExempt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have lEICustomerAccount := readOptional_part [56, 48, 50, 53] record.lEICustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have lEIAlgorithmID := readOptional_part [56, 48, 50, 54] record.lEIAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have customerLEI := readOptional_part [56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have brokerLEI := readOptional_part [56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  simp only [ExecutionReportCross.decode, execTransType, account, avgPx, clOrdId, cumQty, currency, execID, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, transactTime, settlmntTyp, futSettDate, ordRejReason, leavesQty, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, crossType, principalTrade, nonResident, byPass, nCIB, shortMarkingExempt, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, feeCode, some_bind] <;> rfl

theorem ExecutionReportCross.taken (record : ExecutionReportCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdId (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlmntTyp (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.futSettDate (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.lEIOrderOrigination (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 51] record.lEIRoutingArrangementIndicator (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [54, 55, 53, 48] record.uMIRAccountType (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [54, 55, 53, 49] record.uMIRUserID (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 52] record.basketTrade (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 53] record.programTrade (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 55] record.jitney (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 49] record.anonymous (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 51] record.uMIRRegulationID (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 51] record.crossType (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 54] record.principalTrade (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 51] record.nonResident (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 49] record.byPass (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 50] record.nCIB (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [55, 55, 50, 57] record.shortMarkingExempt (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 53] record.lEICustomerAccount (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 54] record.lEIAlgorithmID (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 55] record.customerLEI (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 56] record.brokerLEI (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.feeCode (by decide) (by decide))
                                            (paired_none pairing))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportCrossCrossNew

def ExecutionReportCrossCrossNew.parts (_ : ExecutionReportCrossCrossNew) : List Part :=
  []

def ExecutionReportCrossCrossNew.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportCrossCrossNew.shape (record : ExecutionReportCrossCrossNew) : record.parts.map Part.tags = ExecutionReportCrossCrossNew.tags := rfl

def ExecutionReportCrossCrossNew.decode (_ : List Token) : Option ExecutionReportCrossCrossNew := some {}

theorem ExecutionReportCrossCrossNew.decode_agrees (record : ExecutionReportCrossCrossNew) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportCrossCrossNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCrossCrossNew.decode tokens = some record := by
  rfl

theorem ExecutionReportCrossCrossNew.taken (record : ExecutionReportCrossCrossNew) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure ExecutionReportCrossCrossFill where
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  contraBroker : Option (Terminated 1)  -- tag 375

def ExecutionReportCrossCrossFill.parts (record : ExecutionReportCrossCrossFill) : List Part :=
  [Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.optional [51, 55, 53] record.contraBroker]

def ExecutionReportCrossCrossFill.tags : List (List (List UInt8)) :=
  [[[56, 53, 49]], [[51, 55, 53]]]

theorem ExecutionReportCrossCrossFill.shape (record : ExecutionReportCrossCrossFill) : record.parts.map Part.tags = ExecutionReportCrossCrossFill.tags := rfl

def ExecutionReportCrossCrossFill.decode (tokens : List Token) : Option ExecutionReportCrossCrossFill := do
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  pure { lastLiquidityInd, contraBroker }

theorem ExecutionReportCrossCrossFill.decode_agrees (record : ExecutionReportCrossCrossFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportCrossCrossFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportCrossCrossFill.decode tokens = some record := by
  have distinct : ExecutionReportCrossCrossFill.tags.flatten.Nodup := by decide +kernel
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportCrossCrossFill.decode, lastLiquidityInd, contraBroker, some_bind] <;> rfl

theorem ExecutionReportCrossCrossFill.taken (record : ExecutionReportCrossCrossFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [56, 53, 49] record.lastLiquidityInd (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
    (paired_none pairing))

structure ExecutionReportRegular where
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdId : Terminated 1  -- tag 11
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  execTransType : Terminated 1  -- tag 20
  handlInst : Option (Terminated 1)  -- tag 21
  lastPx : Option (Terminated 1)  -- tag 31
  lastShares : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  settlmntTyp : Option (Terminated 1)  -- tag 63
  futSettDate : Option (Terminated 1)  -- tag 64
  tradeDate : Option (Terminated 1)  -- tag 75
  execBroker : Option (Terminated 1)  -- tag 76
  stopPx : Option (Terminated 1)  -- tag 99
  clientID : Option (Terminated 1)  -- tag 109
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  leavesQty : Terminated 1  -- tag 151
  expireDate : Option (Terminated 1)  -- tag 432
  displayQty : Option (Terminated 1)  -- tag 1138
  lEIOrderOrigination : Option (Terminated 1)  -- tag 1724
  lEIRoutingArrangementIndicator : Option (Terminated 1)  -- tag 2883
  uMIRAccountType : Option (Terminated 1)  -- tag 6750
  uMIRUserID : Option (Terminated 1)  -- tag 6751
  basketTrade : Option (Terminated 1)  -- tag 6754
  programTrade : Option (Terminated 1)  -- tag 6755
  jitney : Option (Terminated 1)  -- tag 6757
  anonymous : Option (Terminated 1)  -- tag 6761
  uMIRRegulationID : Option (Terminated 1)  -- tag 6763
  principalTrade : Option (Terminated 1)  -- tag 6776
  washTradeIndicator : Option (Terminated 1)  -- tag 6777
  nonResident : Option (Terminated 1)  -- tag 6783
  byPass : Option (Terminated 1)  -- tag 6791
  nCIB : Option (Terminated 1)  -- tag 6792
  noTradeFeat : Option (Terminated 1)  -- tag 7713
  noTradeKey : Option (Terminated 1)  -- tag 7714
  shortMarkingExempt : Option (Terminated 1)  -- tag 7729
  conditionalFlag : Option (Terminated 1)  -- tag 8002
  conditionalStatus : Option (Terminated 1)  -- tag 8005
  lEICustomerAccount : Option (Terminated 1)  -- tag 8025
  lEIAlgorithmID : Option (Terminated 1)  -- tag 8026
  customerLEI : Option (Terminated 1)  -- tag 8027
  brokerLEI : Option (Terminated 1)  -- tag 8028
  modifySequence : Option (Terminated 1)  -- tag 9617
  origCompID : Option (Terminated 1)  -- tag 9688
  origSubID : Option (Terminated 1)  -- tag 9689
  feeCode : Option (Terminated 1)  -- tag 9882
  matchingStateParticipation : Option (Terminated 1)  -- tag 20005
  trueMinQty : Option (Terminated 1)  -- tag 22009

def ExecutionReportRegular.parts (record : ExecutionReportRegular) : List Part :=
  [Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdId,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 48] record.execTransType,
   Part.optional [50, 49] record.handlInst,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastShares,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [54, 51] record.settlmntTyp,
   Part.optional [54, 52] record.futSettDate,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [55, 54] record.execBroker,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 55, 50, 52] record.lEIOrderOrigination,
   Part.optional [50, 56, 56, 51] record.lEIRoutingArrangementIndicator,
   Part.optional [54, 55, 53, 48] record.uMIRAccountType,
   Part.optional [54, 55, 53, 49] record.uMIRUserID,
   Part.optional [54, 55, 53, 52] record.basketTrade,
   Part.optional [54, 55, 53, 53] record.programTrade,
   Part.optional [54, 55, 53, 55] record.jitney,
   Part.optional [54, 55, 54, 49] record.anonymous,
   Part.optional [54, 55, 54, 51] record.uMIRRegulationID,
   Part.optional [54, 55, 55, 54] record.principalTrade,
   Part.optional [54, 55, 55, 55] record.washTradeIndicator,
   Part.optional [54, 55, 56, 51] record.nonResident,
   Part.optional [54, 55, 57, 49] record.byPass,
   Part.optional [54, 55, 57, 50] record.nCIB,
   Part.optional [55, 55, 49, 51] record.noTradeFeat,
   Part.optional [55, 55, 49, 52] record.noTradeKey,
   Part.optional [55, 55, 50, 57] record.shortMarkingExempt,
   Part.optional [56, 48, 48, 50] record.conditionalFlag,
   Part.optional [56, 48, 48, 53] record.conditionalStatus,
   Part.optional [56, 48, 50, 53] record.lEICustomerAccount,
   Part.optional [56, 48, 50, 54] record.lEIAlgorithmID,
   Part.optional [56, 48, 50, 55] record.customerLEI,
   Part.optional [56, 48, 50, 56] record.brokerLEI,
   Part.optional [57, 54, 49, 55] record.modifySequence,
   Part.optional [57, 54, 56, 56] record.origCompID,
   Part.optional [57, 54, 56, 57] record.origSubID,
   Part.optional [57, 56, 56, 50] record.feeCode,
   Part.optional [50, 48, 48, 48, 53] record.matchingStateParticipation,
   Part.optional [50, 50, 48, 48, 57] record.trueMinQty]

def ExecutionReportRegular.tags : List (List (List UInt8)) :=
  [[[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 55]], [[49, 56]], [[50, 48]], [[50, 49]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[54, 51]], [[54, 52]], [[55, 53]], [[55, 54]], [[57, 57]], [[49, 48, 57]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[49, 53, 49]], [[52, 51, 50]], [[49, 49, 51, 56]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 53, 48]], [[54, 55, 53, 49]], [[54, 55, 53, 52]], [[54, 55, 53, 53]], [[54, 55, 53, 55]], [[54, 55, 54, 49]], [[54, 55, 54, 51]], [[54, 55, 55, 54]], [[54, 55, 55, 55]], [[54, 55, 56, 51]], [[54, 55, 57, 49]], [[54, 55, 57, 50]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[55, 55, 50, 57]], [[56, 48, 48, 50]], [[56, 48, 48, 53]], [[56, 48, 50, 53]], [[56, 48, 50, 54]], [[56, 48, 50, 55]], [[56, 48, 50, 56]], [[57, 54, 49, 55]], [[57, 54, 56, 56]], [[57, 54, 56, 57]], [[57, 56, 56, 50]], [[50, 48, 48, 48, 53]], [[50, 50, 48, 48, 57]]]

theorem ExecutionReportRegular.shape (record : ExecutionReportRegular) : record.parts.map Part.tags = ExecutionReportRegular.tags := rfl

def ExecutionReportRegular.decode (tokens : List Token) : Option ExecutionReportRegular := do
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let execTransType ← readRequired [50, 48] tokens
  let handlInst ← readOptional [50, 49] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastShares ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let settlmntTyp ← readOptional [54, 51] tokens
  let futSettDate ← readOptional [54, 52] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let execBroker ← readOptional [55, 54] tokens
  let stopPx ← readOptional [57, 57] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let lEIOrderOrigination ← readOptional [49, 55, 50, 52] tokens
  let lEIRoutingArrangementIndicator ← readOptional [50, 56, 56, 51] tokens
  let uMIRAccountType ← readOptional [54, 55, 53, 48] tokens
  let uMIRUserID ← readOptional [54, 55, 53, 49] tokens
  let basketTrade ← readOptional [54, 55, 53, 52] tokens
  let programTrade ← readOptional [54, 55, 53, 53] tokens
  let jitney ← readOptional [54, 55, 53, 55] tokens
  let anonymous ← readOptional [54, 55, 54, 49] tokens
  let uMIRRegulationID ← readOptional [54, 55, 54, 51] tokens
  let principalTrade ← readOptional [54, 55, 55, 54] tokens
  let washTradeIndicator ← readOptional [54, 55, 55, 55] tokens
  let nonResident ← readOptional [54, 55, 56, 51] tokens
  let byPass ← readOptional [54, 55, 57, 49] tokens
  let nCIB ← readOptional [54, 55, 57, 50] tokens
  let noTradeFeat ← readOptional [55, 55, 49, 51] tokens
  let noTradeKey ← readOptional [55, 55, 49, 52] tokens
  let shortMarkingExempt ← readOptional [55, 55, 50, 57] tokens
  let conditionalFlag ← readOptional [56, 48, 48, 50] tokens
  let conditionalStatus ← readOptional [56, 48, 48, 53] tokens
  let lEICustomerAccount ← readOptional [56, 48, 50, 53] tokens
  let lEIAlgorithmID ← readOptional [56, 48, 50, 54] tokens
  let customerLEI ← readOptional [56, 48, 50, 55] tokens
  let brokerLEI ← readOptional [56, 48, 50, 56] tokens
  let modifySequence ← readOptional [57, 54, 49, 55] tokens
  let origCompID ← readOptional [57, 54, 56, 56] tokens
  let origSubID ← readOptional [57, 54, 56, 57] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  let matchingStateParticipation ← readOptional [50, 48, 48, 48, 53] tokens
  let trueMinQty ← readOptional [50, 50, 48, 48, 57] tokens
  pure { account, avgPx, clOrdId, cumQty, execID, execInst, execTransType, handlInst, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, timeInForce, transactTime, settlmntTyp, futSettDate, tradeDate, execBroker, stopPx, clientID, minQty, maxFloor, expireTime, leavesQty, expireDate, displayQty, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, principalTrade, washTradeIndicator, nonResident, byPass, nCIB, noTradeFeat, noTradeKey, shortMarkingExempt, conditionalFlag, conditionalStatus, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, modifySequence, origCompID, origSubID, feeCode, matchingStateParticipation, trueMinQty }

theorem ExecutionReportRegular.decode_agrees (record : ExecutionReportRegular) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegular.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegular.decode tokens = some record := by
  have distinct : ExecutionReportRegular.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have settlmntTyp := readOptional_part [54, 51] record.settlmntTyp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have futSettDate := readOptional_part [54, 52] record.futSettDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have lEIOrderOrigination := readOptional_part [49, 55, 50, 52] record.lEIOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have lEIRoutingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.lEIRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have uMIRAccountType := readOptional_part [54, 55, 53, 48] record.uMIRAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have uMIRUserID := readOptional_part [54, 55, 53, 49] record.uMIRUserID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have basketTrade := readOptional_part [54, 55, 53, 52] record.basketTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have programTrade := readOptional_part [54, 55, 53, 53] record.programTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have jitney := readOptional_part [54, 55, 53, 55] record.jitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have anonymous := readOptional_part [54, 55, 54, 49] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have principalTrade := readOptional_part [54, 55, 55, 54] record.principalTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have washTradeIndicator := readOptional_part [54, 55, 55, 55] record.washTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have nonResident := readOptional_part [54, 55, 56, 51] record.nonResident tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have byPass := readOptional_part [54, 55, 57, 49] record.byPass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have nCIB := readOptional_part [54, 55, 57, 50] record.nCIB tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have shortMarkingExempt := readOptional_part [55, 55, 50, 57] record.shortMarkingExempt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have conditionalFlag := readOptional_part [56, 48, 48, 50] record.conditionalFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have conditionalStatus := readOptional_part [56, 48, 48, 53] record.conditionalStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have lEICustomerAccount := readOptional_part [56, 48, 50, 53] record.lEICustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have lEIAlgorithmID := readOptional_part [56, 48, 50, 54] record.lEIAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have customerLEI := readOptional_part [56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have brokerLEI := readOptional_part [56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have modifySequence := readOptional_part [57, 54, 49, 55] record.modifySequence tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have origCompID := readOptional_part [57, 54, 56, 56] record.origCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have origSubID := readOptional_part [57, 54, 56, 57] record.origSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  have matchingStateParticipation := readOptional_part [50, 48, 48, 48, 53] record.matchingStateParticipation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 58 (by decide +kernel)))
  have trueMinQty := readOptional_part [50, 50, 48, 48, 57] record.trueMinQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 59 (by decide +kernel)))
  simp only [ExecutionReportRegular.decode, account, avgPx, clOrdId, cumQty, execID, execInst, execTransType, handlInst, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, timeInForce, transactTime, settlmntTyp, futSettDate, tradeDate, execBroker, stopPx, clientID, minQty, maxFloor, expireTime, leavesQty, expireDate, displayQty, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, principalTrade, washTradeIndicator, nonResident, byPass, nCIB, noTradeFeat, noTradeKey, shortMarkingExempt, conditionalFlag, conditionalStatus, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, modifySequence, origCompID, origSubID, feeCode, matchingStateParticipation, trueMinQty, some_bind] <;> rfl

theorem ExecutionReportRegular.taken (record : ExecutionReportRegular) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [54] record.avgPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdId (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 49] record.handlInst (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastShares (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlmntTyp (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.futSettDate (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.lEIOrderOrigination (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 51] record.lEIRoutingArrangementIndicator (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 48] record.uMIRAccountType (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 49] record.uMIRUserID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 52] record.basketTrade (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 53] record.programTrade (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 55] record.jitney (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 49] record.anonymous (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 51] record.uMIRRegulationID (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 54] record.principalTrade (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 55] record.washTradeIndicator (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 51] record.nonResident (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 49] record.byPass (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 50] record.nCIB (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [55, 55, 49, 51] record.noTradeFeat (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [55, 55, 49, 52] record.noTradeKey (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [55, 55, 50, 57] record.shortMarkingExempt (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 50] record.conditionalFlag (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 53] record.conditionalStatus (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 53] record.lEICustomerAccount (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 54] record.lEIAlgorithmID (by decide) (by decide))
                                                      (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 55] record.customerLEI (by decide) (by decide))
                                                       (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 56] record.brokerLEI (by decide) (by decide))
                                                        (paired_cons pairing _ _ (paired_optional pairing [57, 54, 49, 55] record.modifySequence (by decide) (by decide))
                                                         (paired_cons pairing _ _ (paired_optional pairing [57, 54, 56, 56] record.origCompID (by decide) (by decide))
                                                          (paired_cons pairing _ _ (paired_optional pairing [57, 54, 56, 57] record.origSubID (by decide) (by decide))
                                                           (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.feeCode (by decide) (by decide))
                                                            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 48, 53] record.matchingStateParticipation (by decide) (by decide))
                                                             (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 48, 57] record.trueMinQty (by decide) (by decide))
                                                              (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

structure ExecutionReportRegularNew

def ExecutionReportRegularNew.parts (_ : ExecutionReportRegularNew) : List Part :=
  []

def ExecutionReportRegularNew.tags : List (List (List UInt8)) :=
  []

theorem ExecutionReportRegularNew.shape (record : ExecutionReportRegularNew) : record.parts.map Part.tags = ExecutionReportRegularNew.tags := rfl

def ExecutionReportRegularNew.decode (_ : List Token) : Option ExecutionReportRegularNew := some {}

theorem ExecutionReportRegularNew.decode_agrees (record : ExecutionReportRegularNew) (tokens : List Token)
    (_ : ∀ tags ∈ ExecutionReportRegularNew.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularNew.decode tokens = some record := by
  rfl

theorem ExecutionReportRegularNew.taken (record : ExecutionReportRegularNew) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

structure ExecutionReportRegularPartialFill where
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  contraBroker : Option (Terminated 1)  -- tag 375
  matchingPriority : Option (Terminated 1)  -- tag 7732
  selfTrade : Option (Terminated 1)  -- tag 7733
  currency : Option (Terminated 1)  -- tag 15

def ExecutionReportRegularPartialFill.parts (record : ExecutionReportRegularPartialFill) : List Part :=
  [Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [55, 55, 51, 50] record.matchingPriority,
   Part.optional [55, 55, 51, 51] record.selfTrade,
   Part.optional [49, 53] record.currency]

def ExecutionReportRegularPartialFill.tags : List (List (List UInt8)) :=
  [[[56, 53, 49]], [[51, 55, 53]], [[55, 55, 51, 50]], [[55, 55, 51, 51]], [[49, 53]]]

theorem ExecutionReportRegularPartialFill.shape (record : ExecutionReportRegularPartialFill) : record.parts.map Part.tags = ExecutionReportRegularPartialFill.tags := rfl

def ExecutionReportRegularPartialFill.decode (tokens : List Token) : Option ExecutionReportRegularPartialFill := do
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let matchingPriority ← readOptional [55, 55, 51, 50] tokens
  let selfTrade ← readOptional [55, 55, 51, 51] tokens
  let currency ← readOptional [49, 53] tokens
  pure { lastLiquidityInd, contraBroker, matchingPriority, selfTrade, currency }

theorem ExecutionReportRegularPartialFill.decode_agrees (record : ExecutionReportRegularPartialFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularPartialFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularPartialFill.decode tokens = some record := by
  have distinct : ExecutionReportRegularPartialFill.tags.flatten.Nodup := by decide +kernel
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have matchingPriority := readOptional_part [55, 55, 51, 50] record.matchingPriority tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have selfTrade := readOptional_part [55, 55, 51, 51] record.selfTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportRegularPartialFill.decode, lastLiquidityInd, contraBroker, matchingPriority, selfTrade, currency, some_bind] <;> rfl

theorem ExecutionReportRegularPartialFill.taken (record : ExecutionReportRegularPartialFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [56, 53, 49] record.lastLiquidityInd (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 50] record.matchingPriority (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 51] record.selfTrade (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
       (paired_none pairing)))))

structure ExecutionReportRegularFill where
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  contraBroker : Option (Terminated 1)  -- tag 375
  matchingPriority : Option (Terminated 1)  -- tag 7732
  selfTrade : Option (Terminated 1)  -- tag 7733
  currency : Option (Terminated 1)  -- tag 15

def ExecutionReportRegularFill.parts (record : ExecutionReportRegularFill) : List Part :=
  [Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [55, 55, 51, 50] record.matchingPriority,
   Part.optional [55, 55, 51, 51] record.selfTrade,
   Part.optional [49, 53] record.currency]

def ExecutionReportRegularFill.tags : List (List (List UInt8)) :=
  [[[56, 53, 49]], [[51, 55, 53]], [[55, 55, 51, 50]], [[55, 55, 51, 51]], [[49, 53]]]

theorem ExecutionReportRegularFill.shape (record : ExecutionReportRegularFill) : record.parts.map Part.tags = ExecutionReportRegularFill.tags := rfl

def ExecutionReportRegularFill.decode (tokens : List Token) : Option ExecutionReportRegularFill := do
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let matchingPriority ← readOptional [55, 55, 51, 50] tokens
  let selfTrade ← readOptional [55, 55, 51, 51] tokens
  let currency ← readOptional [49, 53] tokens
  pure { lastLiquidityInd, contraBroker, matchingPriority, selfTrade, currency }

theorem ExecutionReportRegularFill.decode_agrees (record : ExecutionReportRegularFill) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularFill.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularFill.decode tokens = some record := by
  have distinct : ExecutionReportRegularFill.tags.flatten.Nodup := by decide +kernel
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have matchingPriority := readOptional_part [55, 55, 51, 50] record.matchingPriority tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have selfTrade := readOptional_part [55, 55, 51, 51] record.selfTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [ExecutionReportRegularFill.decode, lastLiquidityInd, contraBroker, matchingPriority, selfTrade, currency, some_bind] <;> rfl

theorem ExecutionReportRegularFill.taken (record : ExecutionReportRegularFill) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [56, 53, 49] record.lastLiquidityInd (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 53] record.contraBroker (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 50] record.matchingPriority (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 51] record.selfTrade (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
       (paired_none pairing)))))

structure ExecutionReportRegularDoneForDay where
  execRestatementReason : Option (Terminated 1)  -- tag 378

def ExecutionReportRegularDoneForDay.parts (record : ExecutionReportRegularDoneForDay) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason]

def ExecutionReportRegularDoneForDay.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]]]

theorem ExecutionReportRegularDoneForDay.shape (record : ExecutionReportRegularDoneForDay) : record.parts.map Part.tags = ExecutionReportRegularDoneForDay.tags := rfl

def ExecutionReportRegularDoneForDay.decode (tokens : List Token) : Option ExecutionReportRegularDoneForDay := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  pure { execRestatementReason }

theorem ExecutionReportRegularDoneForDay.decode_agrees (record : ExecutionReportRegularDoneForDay) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularDoneForDay.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularDoneForDay.decode tokens = some record := by
  have distinct : ExecutionReportRegularDoneForDay.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportRegularDoneForDay.decode, execRestatementReason, some_bind] <;> rfl

theorem ExecutionReportRegularDoneForDay.taken (record : ExecutionReportRegularDoneForDay) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
   (paired_none pairing)

structure ExecutionReportRegularCanceled where
  origClOrdID : Option (Terminated 1)  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  secondaryOrderID : Option (Terminated 1)  -- tag 198

def ExecutionReportRegularCanceled.parts (record : ExecutionReportRegularCanceled) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [49, 57, 56] record.secondaryOrderID]

def ExecutionReportRegularCanceled.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[53, 56]], [[49, 57, 56]]]

theorem ExecutionReportRegularCanceled.shape (record : ExecutionReportRegularCanceled) : record.parts.map Part.tags = ExecutionReportRegularCanceled.tags := rfl

def ExecutionReportRegularCanceled.decode (tokens : List Token) : Option ExecutionReportRegularCanceled := do
  let origClOrdID ← readOptional [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  pure { origClOrdID, text, secondaryOrderID }

theorem ExecutionReportRegularCanceled.decode_agrees (record : ExecutionReportRegularCanceled) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularCanceled.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularCanceled.decode tokens = some record := by
  have distinct : ExecutionReportRegularCanceled.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ExecutionReportRegularCanceled.decode, origClOrdID, text, secondaryOrderID, some_bind] <;> rfl

theorem ExecutionReportRegularCanceled.taken (record : ExecutionReportRegularCanceled) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
     (paired_none pairing)))

structure ExecutionReportRegularReplaced where
  origClOrdID : Option (Terminated 1)  -- tag 41
  secondaryOrderID : Option (Terminated 1)  -- tag 198

def ExecutionReportRegularReplaced.parts (record : ExecutionReportRegularReplaced) : List Part :=
  [Part.optional [52, 49] record.origClOrdID,
   Part.optional [49, 57, 56] record.secondaryOrderID]

def ExecutionReportRegularReplaced.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 57, 56]]]

theorem ExecutionReportRegularReplaced.shape (record : ExecutionReportRegularReplaced) : record.parts.map Part.tags = ExecutionReportRegularReplaced.tags := rfl

def ExecutionReportRegularReplaced.decode (tokens : List Token) : Option ExecutionReportRegularReplaced := do
  let origClOrdID ← readOptional [52, 49] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  pure { origClOrdID, secondaryOrderID }

theorem ExecutionReportRegularReplaced.decode_agrees (record : ExecutionReportRegularReplaced) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularReplaced.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularReplaced.decode tokens = some record := by
  have distinct : ExecutionReportRegularReplaced.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRegularReplaced.decode, origClOrdID, secondaryOrderID, some_bind] <;> rfl

theorem ExecutionReportRegularReplaced.taken (record : ExecutionReportRegularReplaced) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
    (paired_none pairing))

structure ExecutionReportRegularRejected where
  ordRejReason : Option (Terminated 1)  -- tag 103
  text : Option (Terminated 1)  -- tag 58

def ExecutionReportRegularRejected.parts (record : ExecutionReportRegularRejected) : List Part :=
  [Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text]

def ExecutionReportRegularRejected.tags : List (List (List UInt8)) :=
  [[[49, 48, 51]], [[53, 56]]]

theorem ExecutionReportRegularRejected.shape (record : ExecutionReportRegularRejected) : record.parts.map Part.tags = ExecutionReportRegularRejected.tags := rfl

def ExecutionReportRegularRejected.decode (tokens : List Token) : Option ExecutionReportRegularRejected := do
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { ordRejReason, text }

theorem ExecutionReportRegularRejected.decode_agrees (record : ExecutionReportRegularRejected) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularRejected.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularRejected.decode tokens = some record := by
  have distinct : ExecutionReportRegularRejected.tags.flatten.Nodup := by decide +kernel
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRegularRejected.decode, ordRejReason, text, some_bind] <;> rfl

theorem ExecutionReportRegularRejected.taken (record : ExecutionReportRegularRejected) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_none pairing))

structure ExecutionReportRegularRestated where
  execRestatementReason : Option (Terminated 1)  -- tag 378
  secondaryOrderID : Option (Terminated 1)  -- tag 198

def ExecutionReportRegularRestated.parts (record : ExecutionReportRegularRestated) : List Part :=
  [Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [49, 57, 56] record.secondaryOrderID]

def ExecutionReportRegularRestated.tags : List (List (List UInt8)) :=
  [[[51, 55, 56]], [[49, 57, 56]]]

theorem ExecutionReportRegularRestated.shape (record : ExecutionReportRegularRestated) : record.parts.map Part.tags = ExecutionReportRegularRestated.tags := rfl

def ExecutionReportRegularRestated.decode (tokens : List Token) : Option ExecutionReportRegularRestated := do
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let secondaryOrderID ← readOptional [49, 57, 56] tokens
  pure { execRestatementReason, secondaryOrderID }

theorem ExecutionReportRegularRestated.decode_agrees (record : ExecutionReportRegularRestated) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportRegularRestated.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportRegularRestated.decode tokens = some record := by
  have distinct : ExecutionReportRegularRestated.tags.flatten.Nodup := by decide +kernel
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryOrderID := readOptional_part [49, 57, 56] record.secondaryOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReportRegularRestated.decode, execRestatementReason, secondaryOrderID, some_bind] <;> rfl

theorem ExecutionReportRegularRestated.taken (record : ExecutionReportRegularRestated) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57, 56] record.secondaryOrderID (by decide) (by decide))
    (paired_none pairing))

structure CancelReject where
  clOrdId : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  text : Option (Terminated 1)  -- tag 58
  cxlRejReason : Option (Terminated 1)  -- tag 102
  cxlRejResponseTo : Terminated 1  -- tag 434

def CancelReject.parts (record : CancelReject) : List Part :=
  [Part.required [49, 49] record.clOrdId,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.required [52, 51, 52] record.cxlRejResponseTo]

def CancelReject.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 56]], [[49, 48, 50]], [[52, 51, 52]]]

theorem CancelReject.shape (record : CancelReject) : record.parts.map Part.tags = CancelReject.tags := rfl

def CancelReject.decode (tokens : List Token) : Option CancelReject := do
  let clOrdId ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let text ← readOptional [53, 56] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let cxlRejResponseTo ← readRequired [52, 51, 52] tokens
  pure { clOrdId, orderID, ordStatus, origClOrdID, text, cxlRejReason, cxlRejResponseTo }

theorem CancelReject.decode_agrees (record : CancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelReject.decode tokens = some record := by
  have distinct : CancelReject.tags.flatten.Nodup := by decide +kernel
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cxlRejResponseTo := readRequired_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [CancelReject.decode, clOrdId, orderID, ordStatus, origClOrdID, text, cxlRejReason, cxlRejResponseTo, some_bind] <;> rfl

theorem CancelReject.taken (record : CancelReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdId (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50] record.cxlRejReason (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 51, 52] record.cxlRejResponseTo (by decide) (by decide))
         (paired_none pairing)))))))

structure TradeCancelCorrect where
  account : Option (Terminated 1)  -- tag 1
  clOrdId : Terminated 1  -- tag 11
  execID : Terminated 1  -- tag 17
  execRefID : Terminated 1  -- tag 19
  execTransType : Terminated 1  -- tag 20
  lastPx : Terminated 1  -- tag 31
  lastShares : Terminated 1  -- tag 32
  orderID : Terminated 1  -- tag 37
  origTime : Terminated 1  -- tag 42
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60
  symbolSfx : Terminated 1  -- tag 65
  lastLiquidityInd : Terminated 1  -- tag 851
  correctedPrice : Option (Terminated 1)  -- tag 9620
  feeCode : Option (Terminated 1)  -- tag 9882

def TradeCancelCorrect.parts (record : TradeCancelCorrect) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdId,
   Part.required [49, 55] record.execID,
   Part.required [49, 57] record.execRefID,
   Part.required [50, 48] record.execTransType,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastShares,
   Part.required [51, 55] record.orderID,
   Part.required [52, 50] record.origTime,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.required [54, 53] record.symbolSfx,
   Part.required [56, 53, 49] record.lastLiquidityInd,
   Part.optional [57, 54, 50, 48] record.correctedPrice,
   Part.optional [57, 56, 56, 50] record.feeCode]

def TradeCancelCorrect.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 55]], [[49, 57]], [[50, 48]], [[51, 49]], [[51, 50]], [[51, 55]], [[52, 50]], [[53, 52]], [[53, 53]], [[54, 48]], [[54, 53]], [[56, 53, 49]], [[57, 54, 50, 48]], [[57, 56, 56, 50]]]

theorem TradeCancelCorrect.shape (record : TradeCancelCorrect) : record.parts.map Part.tags = TradeCancelCorrect.tags := rfl

def TradeCancelCorrect.decode (tokens : List Token) : Option TradeCancelCorrect := do
  let account ← readOptional [49] tokens
  let clOrdId ← readRequired [49, 49] tokens
  let execID ← readRequired [49, 55] tokens
  let execRefID ← readRequired [49, 57] tokens
  let execTransType ← readRequired [50, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastShares ← readRequired [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let origTime ← readRequired [52, 50] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let symbolSfx ← readRequired [54, 53] tokens
  let lastLiquidityInd ← readRequired [56, 53, 49] tokens
  let correctedPrice ← readOptional [57, 54, 50, 48] tokens
  let feeCode ← readOptional [57, 56, 56, 50] tokens
  pure { account, clOrdId, execID, execRefID, execTransType, lastPx, lastShares, orderID, origTime, side, symbol, transactTime, symbolSfx, lastLiquidityInd, correctedPrice, feeCode }

theorem TradeCancelCorrect.decode_agrees (record : TradeCancelCorrect) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCancelCorrect.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCancelCorrect.decode tokens = some record := by
  have distinct : TradeCancelCorrect.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdId := readRequired_part [49, 49] record.clOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execRefID := readRequired_part [49, 57] record.execRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastShares := readRequired_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origTime := readRequired_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbolSfx := readRequired_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have lastLiquidityInd := readRequired_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have correctedPrice := readOptional_part [57, 54, 50, 48] record.correctedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [TradeCancelCorrect.decode, account, clOrdId, execID, execRefID, execTransType, lastPx, lastShares, orderID, origTime, side, symbol, transactTime, symbolSfx, lastLiquidityInd, correctedPrice, feeCode, some_bind] <;> rfl

theorem TradeCancelCorrect.taken (record : TradeCancelCorrect) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdId (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 57] record.execRefID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [50, 48] record.execTransType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastShares (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 50] record.origTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [54, 53] record.symbolSfx (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [56, 53, 49] record.lastLiquidityInd (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [57, 54, 50, 48] record.correctedPrice (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 56, 56, 50] record.feeCode (by decide) (by decide))
                  (paired_none pairing))))))))))))))))

inductive Message where
  | executionReportCrossCrossNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossNew)
  | executionReportCrossCrossFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossFill)
  | executionReportRegularNew (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularNew)
  | executionReportRegularPartialFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularPartialFill)
  | executionReportRegularFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularFill)
  | executionReportRegularDoneForDay (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularDoneForDay)
  | executionReportRegularCanceled (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularCanceled)
  | executionReportRegularReplaced (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularReplaced)
  | executionReportRegularRejected (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRejected)
  | executionReportRegularRestated (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRestated)
  | cancelReject (header : Header) (r0 : CancelReject)
  | tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect)

def Message.tokens : Message → List Token
  | .executionReportCrossCrossNew header r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts)
  | .executionReportCrossCrossFill header r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts)
  | .executionReportRegularNew header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts)
  | .executionReportRegularPartialFill header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts)
  | .executionReportRegularFill header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts)
  | .executionReportRegularDoneForDay header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts)
  | .executionReportRegularCanceled header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts)
  | .executionReportRegularReplaced header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts)
  | .executionReportRegularRejected header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts)
  | .executionReportRegularRestated header k0 r0 r1 r2 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts)
  | .cancelReject header r0 => ⟨[51, 53], [57]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCancelCorrect header r0 => ⟨[51, 53], [85, 67, 67]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [56] then
        match readRequired [49, 48, 48] rest with
        | none => none
        | some key =>
          if h0_0 : key.val = [67] then
            match readRequired [49, 53, 48] rest with
            | none => none
            | some key =>
              if key.val = [48] then
                if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rest then do
                  let header ← Header.decode rest
                  let r0 ← ExecutionReport.decode rest
                  let r1 ← ExecutionReportCross.decode rest
                  let r2 ← ExecutionReportCrossCrossNew.decode rest
                  pure (.executionReportCrossCrossNew header r0 r1 r2)
                else none
              else if key.val = [50] then
                if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rest then do
                  let header ← Header.decode rest
                  let r0 ← ExecutionReport.decode rest
                  let r1 ← ExecutionReportCross.decode rest
                  let r2 ← ExecutionReportCrossCrossFill.decode rest
                  pure (.executionReportCrossCrossFill header r0 r1 r2)
                else none
              else none
          else let k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))} := ⟨key, by simp [h0_0]⟩
          match readRequired [49, 53, 48] rest with
          | none => none
          | some key =>
            if key.val = [48] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularNew.decode rest
                pure (.executionReportRegularNew header k0 r0 r1 r2)
              else none
            else if key.val = [49] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularPartialFill.decode rest
                pure (.executionReportRegularPartialFill header k0 r0 r1 r2)
              else none
            else if key.val = [50] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularFill.decode rest
                pure (.executionReportRegularFill header k0 r0 r1 r2)
              else none
            else if key.val = [51] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularDoneForDay.decode rest
                pure (.executionReportRegularDoneForDay header k0 r0 r1 r2)
              else none
            else if key.val = [52] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularCanceled.decode rest
                pure (.executionReportRegularCanceled header k0 r0 r1 r2)
              else none
            else if key.val = [53] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularReplaced.decode rest
                pure (.executionReportRegularReplaced header k0 r0 r1 r2)
              else none
            else if key.val = [56] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularRejected.decode rest
                pure (.executionReportRegularRejected header k0 r0 r1 r2)
              else none
            else if key.val = [68] then
              if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rest then do
                let header ← Header.decode rest
                let r0 ← ExecutionReport.decode rest
                let r1 ← ExecutionReportRegular.decode rest
                let r2 ← ExecutionReportRegularRestated.decode rest
                pure (.executionReportRegularRestated header k0 r0 r1 r2)
              else none
            else none
      else if token.value = [57] then
        if known (Header.tags ++ CancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelReject.decode rest
          pure (.cancelReject header r0)
        else none
      else if token.value = [85, 67, 67] then
        if known (Header.tags ++ TradeCancelCorrect.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCancelCorrect.decode rest
          pure (.tradeCancelCorrect header r0)
        else none
      else none
    else none

theorem Message.decode_executionReportCrossCrossNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossNew) :
    Message.decode (Message.tokens (.executionReportCrossCrossNew header r0 r1 r2)) = some (.executionReportCrossCrossNew header r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCross.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportCross.tags) ([[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags) ([[[49, 53, 48]]]) (ExecutionReportCrossCrossNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportCrossCrossNew.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]]) (ExecutionReportCrossCrossNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossNew.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportCrossCrossFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossFill) :
    Message.decode (Message.tokens (.executionReportCrossCrossFill header r0 r1 r2)) = some (.executionReportCrossCrossFill header r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] ⟨[67], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportCross.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportCross.tags) ([[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags) ([[[49, 53, 48]]]) (ExecutionReportCrossCrossFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportCrossCrossFill.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]]) (ExecutionReportCrossCrossFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportCross.tags ++ [[[49, 53, 48]]] ++ ExecutionReportCrossCrossFill.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_executionReportRegularNew (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularNew) :
    Message.decode (Message.tokens (.executionReportRegularNew header k0 r0 r1 r2)) = some (.executionReportRegularNew header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[48], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularNew.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularNew.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularNew.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularNew.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularPartialFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularPartialFill) :
    Message.decode (Message.tokens (.executionReportRegularPartialFill header k0 r0 r1 r2)) = some (.executionReportRegularPartialFill header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[49], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularPartialFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularPartialFill.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularPartialFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularPartialFill.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularFill) :
    Message.decode (Message.tokens (.executionReportRegularFill header k0 r0 r1 r2)) = some (.executionReportRegularFill header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[50], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularFill.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularFill.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularFill.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularFill.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularDoneForDay (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularDoneForDay) :
    Message.decode (Message.tokens (.executionReportRegularDoneForDay header k0 r0 r1 r2)) = some (.executionReportRegularDoneForDay header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[51], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularDoneForDay.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularDoneForDay.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularDoneForDay.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularDoneForDay.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularCanceled (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularCanceled) :
    Message.decode (Message.tokens (.executionReportRegularCanceled header k0 r0 r1 r2)) = some (.executionReportRegularCanceled header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[52], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularCanceled.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularCanceled.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularCanceled.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularCanceled.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularReplaced (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularReplaced) :
    Message.decode (Message.tokens (.executionReportRegularReplaced header k0 r0 r1 r2)) = some (.executionReportRegularReplaced header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[53], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularReplaced.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularReplaced.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularReplaced.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularReplaced.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularRejected (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRejected) :
    Message.decode (Message.tokens (.executionReportRegularRejected header k0 r0 r1 r2)) = some (.executionReportRegularRejected header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularRejected.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularRejected.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularRejected.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRejected.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_executionReportRegularRestated (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRestated) :
    Message.decode (Message.tokens (.executionReportRegularRestated header k0 r0 r1 r2)) = some (.executionReportRegularRestated header k0 r0 r1 r2) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 48, 48] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 48, 48]]]) (ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportRegular.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1]) (r1.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]]) (ExecutionReportRegular.tags) ([[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rfl rfl (by decide +kernel))
  have c4 := readRequired_part [49, 53, 48] ⟨[68], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags) ([[[49, 53, 48]]]) (ExecutionReportRegularRestated.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c5 := ExecutionReportRegularRestated.decode_agrees r2 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r2.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]]) (ExecutionReportRegularRestated.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 48, 48]]] ++ ExecutionReportRegular.tags ++ [[[49, 53, 48]]] ++ ExecutionReportRegularRestated.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 c4 c5 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, c4, c5, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decode (Message.tokens (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := CancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect) :
    Message.decode (Message.tokens (.tradeCancelCorrect header r0)) = some (.tradeCancelCorrect header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrect.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCancelCorrect.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCancelCorrect.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCancelCorrect.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportCrossCrossNew header r0 r1 r2 => exact Message.decode_executionReportCrossCrossNew header r0 r1 r2
  | executionReportCrossCrossFill header r0 r1 r2 => exact Message.decode_executionReportCrossCrossFill header r0 r1 r2
  | executionReportRegularNew header k0 r0 r1 r2 => exact Message.decode_executionReportRegularNew header k0 r0 r1 r2
  | executionReportRegularPartialFill header k0 r0 r1 r2 => exact Message.decode_executionReportRegularPartialFill header k0 r0 r1 r2
  | executionReportRegularFill header k0 r0 r1 r2 => exact Message.decode_executionReportRegularFill header k0 r0 r1 r2
  | executionReportRegularDoneForDay header k0 r0 r1 r2 => exact Message.decode_executionReportRegularDoneForDay header k0 r0 r1 r2
  | executionReportRegularCanceled header k0 r0 r1 r2 => exact Message.decode_executionReportRegularCanceled header k0 r0 r1 r2
  | executionReportRegularReplaced header k0 r0 r1 r2 => exact Message.decode_executionReportRegularReplaced header k0 r0 r1 r2
  | executionReportRegularRejected header k0 r0 r1 r2 => exact Message.decode_executionReportRegularRejected header k0 r0 r1 r2
  | executionReportRegularRestated header k0 r0 r1 r2 => exact Message.decode_executionReportRegularRestated header k0 r0 r1 r2
  | cancelReject header r0 => exact Message.decode_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decode_tradeCancelCorrect header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportCrossCrossNew (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossNew) :
    Message.decodeBytes (Message.encode (.executionReportCrossCrossNew header r0 r1 r2)) = some (.executionReportCrossCrossNew header r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] ⟨[67], by decide⟩) [] (paired_required pairing [49, 48, 48] ⟨[67], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (ExecutionReportCross.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportCrossCrossNew.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCrossCrossNew header r0 r1 r2

theorem Message.decodeBytes_executionReportCrossCrossFill (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportCross) (r2 : ExecutionReportCrossCrossFill) :
    Message.decodeBytes (Message.encode (.executionReportCrossCrossFill header r0 r1 r2)) = some (.executionReportCrossCrossFill header r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] ⟨[67], by decide⟩] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] ⟨[67], by decide⟩]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] ⟨[67], by decide⟩) [] (paired_required pairing [49, 48, 48] ⟨[67], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (ExecutionReportCross.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[50], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportCrossCrossFill.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportCrossCrossFill header r0 r1 r2

theorem Message.decodeBytes_executionReportRegularNew (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularNew) :
    Message.decodeBytes (Message.encode (.executionReportRegularNew header k0 r0 r1 r2)) = some (.executionReportRegularNew header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[48], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[48], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[48], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[48], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularNew.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularNew header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularPartialFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularPartialFill) :
    Message.decodeBytes (Message.encode (.executionReportRegularPartialFill header k0 r0 r1 r2)) = some (.executionReportRegularPartialFill header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[49], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[49], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[49], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[49], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularPartialFill.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularPartialFill header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularFill (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularFill) :
    Message.decodeBytes (Message.encode (.executionReportRegularFill header k0 r0 r1 r2)) = some (.executionReportRegularFill header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[50], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[50], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[50], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[50], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularFill.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularFill header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularDoneForDay (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularDoneForDay) :
    Message.decodeBytes (Message.encode (.executionReportRegularDoneForDay header k0 r0 r1 r2)) = some (.executionReportRegularDoneForDay header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[51], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[51], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[51], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[51], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularDoneForDay.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularDoneForDay header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularCanceled (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularCanceled) :
    Message.decodeBytes (Message.encode (.executionReportRegularCanceled header k0 r0 r1 r2)) = some (.executionReportRegularCanceled header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[52], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[52], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[52], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[52], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularCanceled.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularCanceled header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularReplaced (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularReplaced) :
    Message.decodeBytes (Message.encode (.executionReportRegularReplaced header k0 r0 r1 r2)) = some (.executionReportRegularReplaced header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[53], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[53], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[53], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[53], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularReplaced.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularReplaced header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularRejected (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRejected) :
    Message.decodeBytes (Message.encode (.executionReportRegularRejected header k0 r0 r1 r2)) = some (.executionReportRegularRejected header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[56], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[56], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[56], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[56], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularRejected.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularRejected header k0 r0 r1 r2

theorem Message.decodeBytes_executionReportRegularRestated (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[67]] : List (List UInt8))}) (r0 : ExecutionReport) (r1 : ExecutionReportRegular) (r2 : ExecutionReportRegularRestated) :
    Message.decodeBytes (Message.encode (.executionReportRegularRestated header k0 r0 r1 r2)) = some (.executionReportRegularRestated header k0 r0 r1 r2) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [49, 48, 48] k0.1] ++ r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (ExecutionReport.taken r0) (paired_parts pairing ([Part.required [49, 48, 48] k0.1]) (r1.parts ++ [Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (paired_cons pairing (Part.required [49, 48, 48] k0.1) [] (paired_required pairing [49, 48, 48] k0.1 (by decide) (by decide)) (paired_none pairing)) (paired_parts pairing (r1.parts) ([Part.required [49, 53, 48] ⟨[68], by decide⟩] ++ r2.parts) (ExecutionReportRegular.taken r1) (paired_parts pairing ([Part.required [49, 53, 48] ⟨[68], by decide⟩]) (r2.parts) (paired_cons pairing (Part.required [49, 53, 48] ⟨[68], by decide⟩) [] (paired_required pairing [49, 53, 48] ⟨[68], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (ExecutionReportRegularRestated.taken r2))))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportRegularRestated header k0 r0 r1 r2

theorem Message.decodeBytes_cancelReject (header : Header) (r0 : CancelReject) :
    Message.decodeBytes (Message.encode (.cancelReject header r0)) = some (.cancelReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [57]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (CancelReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelReject header r0

theorem Message.decodeBytes_tradeCancelCorrect (header : Header) (r0 : TradeCancelCorrect) :
    Message.decodeBytes (Message.encode (.tradeCancelCorrect header r0)) = some (.tradeCancelCorrect header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCancelCorrect.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCancelCorrect header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportCrossCrossNew header r0 r1 r2 => exact Message.decodeBytes_executionReportCrossCrossNew header r0 r1 r2
  | executionReportCrossCrossFill header r0 r1 r2 => exact Message.decodeBytes_executionReportCrossCrossFill header r0 r1 r2
  | executionReportRegularNew header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularNew header k0 r0 r1 r2
  | executionReportRegularPartialFill header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularPartialFill header k0 r0 r1 r2
  | executionReportRegularFill header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularFill header k0 r0 r1 r2
  | executionReportRegularDoneForDay header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularDoneForDay header k0 r0 r1 r2
  | executionReportRegularCanceled header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularCanceled header k0 r0 r1 r2
  | executionReportRegularReplaced header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularReplaced header k0 r0 r1 r2
  | executionReportRegularRejected header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularRejected header k0 r0 r1 r2
  | executionReportRegularRestated header k0 r0 r1 r2 => exact Message.decodeBytes_executionReportRegularRestated header k0 r0 r1 r2
  | cancelReject header r0 => exact Message.decodeBytes_cancelReject header r0
  | tradeCancelCorrect header r0 => exact Message.decodeBytes_tradeCancelCorrect header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeMatchnowOrderentryFixV10Exchange
