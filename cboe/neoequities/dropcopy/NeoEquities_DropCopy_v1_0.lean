import Wire

/-!
# Chicago Board Options Exchange Drop Copy v1.0

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeNeoequitiesDropcopyFixV10

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

structure CrossOrderExecutionReport where
  execTransType : Terminated 1  -- tag 20
  account : Option (Terminated 1)  -- tag 1
  avgPx : Terminated 1  -- tag 6
  clOrdID : Terminated 1  -- tag 11
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
  exDestination : Option (Terminated 1)  -- tag 100
  ordRejReason : Option (Terminated 1)  -- tag 103
  execType : Terminated 1  -- tag 150
  leavesQty : Terminated 1  -- tag 151
  contraBroker : Option (Terminated 1)  -- tag 375
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
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

def CrossOrderExecutionReport.parts (record : CrossOrderExecutionReport) : List Part :=
  [Part.required [50, 48] record.execTransType,
   Part.optional [49] record.account,
   Part.required [54] record.avgPx,
   Part.required [49, 49] record.clOrdID,
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
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.required [49, 53, 48] record.execType,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [51, 55, 53] record.contraBroker,
   Part.optional [56, 53, 49] record.lastLiquidityInd,
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

def CrossOrderExecutionReport.tags : List (List (List UInt8)) :=
  [[[50, 48]], [[49]], [[54]], [[49, 49]], [[49, 52]], [[49, 53]], [[49, 55]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[51, 57]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[54, 48]], [[54, 51]], [[54, 52]], [[49, 48, 48]], [[49, 48, 51]], [[49, 53, 48]], [[49, 53, 49]], [[51, 55, 53]], [[56, 53, 49]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 53, 48]], [[54, 55, 53, 49]], [[54, 55, 53, 52]], [[54, 55, 53, 53]], [[54, 55, 53, 55]], [[54, 55, 54, 49]], [[54, 55, 54, 51]], [[54, 55, 55, 51]], [[54, 55, 55, 54]], [[54, 55, 56, 51]], [[54, 55, 57, 49]], [[54, 55, 57, 50]], [[55, 55, 50, 57]], [[56, 48, 50, 53]], [[56, 48, 50, 54]], [[56, 48, 50, 55]], [[56, 48, 50, 56]], [[57, 56, 56, 50]]]

theorem CrossOrderExecutionReport.shape (record : CrossOrderExecutionReport) : record.parts.map Part.tags = CrossOrderExecutionReport.tags := rfl

def CrossOrderExecutionReport.decode (tokens : List Token) : Option CrossOrderExecutionReport := do
  let execTransType ← readRequired [50, 48] tokens
  let account ← readOptional [49] tokens
  let avgPx ← readRequired [54] tokens
  let clOrdID ← readRequired [49, 49] tokens
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
  let exDestination ← readOptional [49, 48, 48] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let contraBroker ← readOptional [51, 55, 53] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
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
  pure { execTransType, account, avgPx, clOrdID, cumQty, currency, execID, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, transactTime, settlmntTyp, futSettDate, exDestination, ordRejReason, execType, leavesQty, contraBroker, lastLiquidityInd, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, crossType, principalTrade, nonResident, byPass, nCIB, shortMarkingExempt, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, feeCode }

theorem CrossOrderExecutionReport.decode_agrees (record : CrossOrderExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ CrossOrderExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CrossOrderExecutionReport.decode tokens = some record := by
  have distinct : CrossOrderExecutionReport.tags.flatten.Nodup := by decide +kernel
  have execTransType := readRequired_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have avgPx := readRequired_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
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
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have contraBroker := readOptional_part [51, 55, 53] record.contraBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have lEIOrderOrigination := readOptional_part [49, 55, 50, 52] record.lEIOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have lEIRoutingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.lEIRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have uMIRAccountType := readRequired_part [54, 55, 53, 48] record.uMIRAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have uMIRUserID := readRequired_part [54, 55, 53, 49] record.uMIRUserID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have basketTrade := readOptional_part [54, 55, 53, 52] record.basketTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have programTrade := readOptional_part [54, 55, 53, 53] record.programTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have jitney := readOptional_part [54, 55, 53, 55] record.jitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have anonymous := readOptional_part [54, 55, 54, 49] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have crossType := readOptional_part [54, 55, 55, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have principalTrade := readOptional_part [54, 55, 55, 54] record.principalTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have nonResident := readOptional_part [54, 55, 56, 51] record.nonResident tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have byPass := readOptional_part [54, 55, 57, 49] record.byPass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have nCIB := readOptional_part [54, 55, 57, 50] record.nCIB tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have shortMarkingExempt := readOptional_part [55, 55, 50, 57] record.shortMarkingExempt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have lEICustomerAccount := readOptional_part [56, 48, 50, 53] record.lEICustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have lEIAlgorithmID := readOptional_part [56, 48, 50, 54] record.lEIAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have customerLEI := readOptional_part [56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have brokerLEI := readOptional_part [56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have feeCode := readOptional_part [57, 56, 56, 50] record.feeCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  simp only [CrossOrderExecutionReport.decode, execTransType, account, avgPx, clOrdID, cumQty, currency, execID, lastPx, lastShares, orderID, orderQty, ordStatus, ordType, price, side, symbol, text, transactTime, settlmntTyp, futSettDate, exDestination, ordRejReason, execType, leavesQty, contraBroker, lastLiquidityInd, lEIOrderOrigination, lEIRoutingArrangementIndicator, uMIRAccountType, uMIRUserID, basketTrade, programTrade, jitney, anonymous, uMIRRegulationID, crossType, principalTrade, nonResident, byPass, nCIB, shortMarkingExempt, lEICustomerAccount, lEIAlgorithmID, customerLEI, brokerLEI, feeCode, some_bind] <;> rfl

inductive Message where
  | crossOrderExecutionReport (header : Header) (r0 : CrossOrderExecutionReport)

def Message.tokens : Message → List Token
  | .crossOrderExecutionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        if known (Header.tags ++ CrossOrderExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CrossOrderExecutionReport.decode rest
          pure (.crossOrderExecutionReport header r0)
        else none
      else none
    else none

theorem Message.decode_crossOrderExecutionReport (header : Header) (r0 : CrossOrderExecutionReport) :
    Message.decode (Message.tokens (.crossOrderExecutionReport header r0)) = some (.crossOrderExecutionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CrossOrderExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := CrossOrderExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CrossOrderExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CrossOrderExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | crossOrderExecutionReport header r0 => exact Message.decode_crossOrderExecutionReport header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_crossOrderExecutionReport (header : Header) (r0 : CrossOrderExecutionReport) :
    Message.decodeBytes (Message.encode (.crossOrderExecutionReport header r0)) = some (.crossOrderExecutionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CrossOrderExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_crossOrderExecutionReport header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | crossOrderExecutionReport header r0 => exact Message.decodeBytes_crossOrderExecutionReport header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeNeoequitiesDropcopyFixV10
