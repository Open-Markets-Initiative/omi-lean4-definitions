import Wire

/-!
# New York Stock Exchange NYSE Pillar Options Floor Broker OMS Open Outcry v2.6, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NyseArcaoptionsFloorbrokerFixV26Client

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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  selfTradeType : Option (Terminated 1)  -- tag 7928
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  pure { account, clOrdID, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, clearingFirm, clearingAccount, optionalData, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  openClose : Terminated 1  -- tag 77
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  noTradingSessions : List NoTradingSessions  -- tag 386
  selfTradeType : Option (Terminated 1)  -- tag 7928
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Terminated 1  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 55] record.openClose,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.required [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [51, 56, 54] :: NoTradingSessions.members, [[55, 57, 50, 56]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let openClose ← readRequired [55, 55] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readRequired [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  pure { account, clOrdID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, selfTradeType, clearingFirm, clearingAccount, optionalData, specialOrdType, extendedExecInst, introducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have extendedExecInst := readRequired_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, orderQty, ordType, origClOrdID, price, side, symbol, text, timeInForce, transactTime, openClose, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, noTradingSessions, selfTradeType, clearingFirm, clearingAccount, optionalData, specialOrdType, extendedExecInst, introducingBadgeID, percentageStrike, percentagePrice, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, some_bind] <;> rfl

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legPositionEffect : Terminated 1  -- tag 564
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Terminated 1  -- tag 611
  legStrikePrice : Terminated 1  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  legRefID : Terminated 1  -- tag 654
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.required [53, 54, 52] record.legPositionEffect,
   Part.required [54, 48, 56] record.legCFICode,
   Part.required [54, 49, 49] record.legMaturityDate,
   Part.required [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.required [54, 53, 52] record.legRefID,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[53, 54, 52]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[54, 53, 52]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legPositionEffect ← readRequired [53, 54, 52] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readRequired [54, 49, 49] tokens
  let legStrikePrice ← readRequired [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  pure { legSymbol, legPositionEffect, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID, percentageStrike, percentagePrice }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legPositionEffect := readRequired_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legMaturityDate := readRequired_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legStrikePrice := readRequired_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legPositionEffect, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, legRefID, percentageStrike, percentagePrice, some_bind] <;> rfl

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

structure NewOrderMultileg where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  noLegs : List NoLegs  -- tag 555
  selfTradeType : Option (Terminated 1)  -- tag 7928
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Terminated 1  -- tag 9448
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 56]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 52]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [53, 53, 53] :: NoLegs.members, [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]]]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  pure { account, clOrdID, orderQty, ordType, price, text, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, account, clOrdID, orderQty, ordType, price, text, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, some_bind] <;> rfl

structure MultilegOrderCancelReplace where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Terminated 1  -- tag 59
  transactTime : Option (Terminated 1)  -- tag 60
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  noTradingSessions : List NoTradingSessions  -- tag 386
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  noLegs : List NoLegs  -- tag 555
  selfTradeType : Option (Terminated 1)  -- tag 7928
  specialOrdType : Option (Terminated 1)  -- tag 9202
  extendedExecInst : Option (Terminated 1)  -- tag 9416
  introducingBadgeID : Option (Terminated 1)  -- tag 9448
  tiedHedgeIndicator : Option (Terminated 1)  -- tag 20032
  tiedToStock : Option (Terminated 1)  -- tag 20035
  refDelta : Option (Terminated 1)  -- tag 20037
  stockPrice : Option (Terminated 1)  -- tag 20038
  stockQty : Option (Terminated 1)  -- tag 20039
  packageLinkID : Option (Terminated 1)  -- tag 20040

def MultilegOrderCancelReplace.parts (record : MultilegOrderCancelReplace) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.required [53, 57] record.timeInForce,
   Part.optional [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.group [51, 56, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within record.noTradingSessions,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.optional [55, 57, 50, 56] record.selfTradeType,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 52, 49, 54] record.extendedExecInst,
   Part.optional [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [50, 48, 48, 51, 50] record.tiedHedgeIndicator,
   Part.optional [50, 48, 48, 51, 53] record.tiedToStock,
   Part.optional [50, 48, 48, 51, 55] record.refDelta,
   Part.optional [50, 48, 48, 51, 56] record.stockPrice,
   Part.optional [50, 48, 48, 51, 57] record.stockQty,
   Part.optional [50, 48, 48, 52, 48] record.packageLinkID]

def MultilegOrderCancelReplace.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 56]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[50, 48, 52]], [51, 56, 54] :: NoTradingSessions.members, [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [53, 53, 53] :: NoLegs.members, [[55, 57, 50, 56]], [[57, 50, 48, 50]], [[57, 52, 49, 54]], [[57, 52, 52, 56]], [[50, 48, 48, 51, 50]], [[50, 48, 48, 51, 53]], [[50, 48, 48, 51, 55]], [[50, 48, 48, 51, 56]], [[50, 48, 48, 51, 57]], [[50, 48, 48, 52, 48]]]

theorem MultilegOrderCancelReplace.shape (record : MultilegOrderCancelReplace) : record.parts.map Part.tags = MultilegOrderCancelReplace.tags := rfl

def MultilegOrderCancelReplace.decode (tokens : List Token) : Option MultilegOrderCancelReplace := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readOptional [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let noTradingSessions ← readGroup [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.decode tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  let selfTradeType ← readOptional [55, 57, 50, 56] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let extendedExecInst ← readOptional [57, 52, 49, 54] tokens
  let introducingBadgeID ← readOptional [57, 52, 52, 56] tokens
  let tiedHedgeIndicator ← readOptional [50, 48, 48, 51, 50] tokens
  let tiedToStock ← readOptional [50, 48, 48, 51, 53] tokens
  let refDelta ← readOptional [50, 48, 48, 51, 55] tokens
  let stockPrice ← readOptional [50, 48, 48, 51, 56] tokens
  let stockQty ← readOptional [50, 48, 48, 51, 57] tokens
  let packageLinkID ← readOptional [50, 48, 48, 52, 48] tokens
  pure { account, clOrdID, orderQty, ordType, origClOrdID, price, text, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID }

theorem MultilegOrderCancelReplace.decode_agrees (record : MultilegOrderCancelReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegOrderCancelReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegOrderCancelReplace.decode tokens = some record := by
  have distinct : MultilegOrderCancelReplace.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noTradingSessions := readGroup_part [51, 56, 54] [51, 51, 54] NoTradingSessions.members NoTradingSessions.encode NoTradingSessions.within NoTradingSessions.decode NoTradingSessions.decode_encode NoTradingSessions.led record.noTradingSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have selfTradeType := readOptional_part [55, 57, 50, 56] record.selfTradeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have extendedExecInst := readOptional_part [57, 52, 49, 54] record.extendedExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have introducingBadgeID := readOptional_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have tiedHedgeIndicator := readOptional_part [50, 48, 48, 51, 50] record.tiedHedgeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have tiedToStock := readOptional_part [50, 48, 48, 51, 53] record.tiedToStock tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have refDelta := readOptional_part [50, 48, 48, 51, 55] record.refDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have stockPrice := readOptional_part [50, 48, 48, 51, 56] record.stockPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have stockQty := readOptional_part [50, 48, 48, 51, 57] record.stockQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have packageLinkID := readOptional_part [50, 48, 48, 52, 48] record.packageLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  simp only [MultilegOrderCancelReplace.decode, account, clOrdID, orderQty, ordType, origClOrdID, price, text, timeInForce, transactTime, securityType, customerOrFirm, noTradingSessions, clearingFirm, clearingAccount, optionalData, noLegs, selfTradeType, specialOrdType, extendedExecInst, introducingBadgeID, tiedHedgeIndicator, tiedToStock, refDelta, stockPrice, stockQty, packageLinkID, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  origClOrdID : Terminated 1  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  pure { clOrdID, origClOrdID, side, symbol, transactTime }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, origClOrdID, side, symbol, transactTime, some_bind] <;> rfl

structure OMSExecutionReport

def OMSExecutionReport.parts (_ : OMSExecutionReport) : List Part :=
  []

def OMSExecutionReport.tags : List (List (List UInt8)) :=
  []

theorem OMSExecutionReport.shape (record : OMSExecutionReport) : record.parts.map Part.tags = OMSExecutionReport.tags := rfl

def OMSExecutionReport.decode (_ : List Token) : Option OMSExecutionReport := some {}

theorem OMSExecutionReport.decode_agrees (record : OMSExecutionReport) (tokens : List Token)
    (_ : ∀ tags ∈ OMSExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OMSExecutionReport.decode tokens = some record := by
  rfl

structure OMSExecutionReportTradeRequest where
  clOrdID : Terminated 1  -- tag 11
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  tradeCondition : Terminated 1  -- tag 277
  introducingBadgeID : Terminated 1  -- tag 9448
  percentageStrike : Option (Terminated 1)  -- tag 20030
  percentagePrice : Option (Terminated 1)  -- tag 20031

def OMSExecutionReportTradeRequest.parts (record : OMSExecutionReportTradeRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [50, 55, 55] record.tradeCondition,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.optional [50, 48, 48, 51, 48] record.percentageStrike,
   Part.optional [50, 48, 48, 51, 49] record.percentagePrice]

def OMSExecutionReportTradeRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 52]], [[53, 53]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [[50, 55, 55]], [[57, 52, 52, 56]], [[50, 48, 48, 51, 48]], [[50, 48, 48, 51, 49]]]

theorem OMSExecutionReportTradeRequest.shape (record : OMSExecutionReportTradeRequest) : record.parts.map Part.tags = OMSExecutionReportTradeRequest.tags := rfl

def OMSExecutionReportTradeRequest.decode (tokens : List Token) : Option OMSExecutionReportTradeRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let tradeCondition ← readRequired [50, 55, 55] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let percentageStrike ← readOptional [50, 48, 48, 51, 48] tokens
  let percentagePrice ← readOptional [50, 48, 48, 51, 49] tokens
  pure { clOrdID, lastPx, lastQty, orderID, ordStatus, origClOrdID, side, symbol, maturityMonthYear, putOrCall, strikePrice, maturityDay, tradeCondition, introducingBadgeID, percentageStrike, percentagePrice }

theorem OMSExecutionReportTradeRequest.decode_agrees (record : OMSExecutionReportTradeRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OMSExecutionReportTradeRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OMSExecutionReportTradeRequest.decode tokens = some record := by
  have distinct : OMSExecutionReportTradeRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradeCondition := readRequired_part [50, 55, 55] record.tradeCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have percentageStrike := readOptional_part [50, 48, 48, 51, 48] record.percentageStrike tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have percentagePrice := readOptional_part [50, 48, 48, 51, 49] record.percentagePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [OMSExecutionReportTradeRequest.decode, clOrdID, lastPx, lastQty, orderID, ordStatus, origClOrdID, side, symbol, maturityMonthYear, putOrCall, strikePrice, maturityDay, tradeCondition, introducingBadgeID, percentageStrike, percentagePrice, some_bind] <;> rfl

structure OMSExecutionReportFLEXPriceRequest where
  clOrdID : Terminated 1  -- tag 11
  lastPx : Option (Terminated 1)  -- tag 31
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  symbol : Terminated 1  -- tag 55
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  introducingBadgeID : Terminated 1  -- tag 9448
  referencePrice : Terminated 1  -- tag 20045
  refDealID : Option (Terminated 1)  -- tag 30002

def OMSExecutionReportFLEXPriceRequest.parts (record : OMSExecutionReportFLEXPriceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 49] record.lastPx,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 53] record.symbol,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [50, 48, 48, 52, 53] record.referencePrice,
   Part.optional [51, 48, 48, 48, 50] record.refDealID]

def OMSExecutionReportFLEXPriceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 49]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 53]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [[57, 52, 52, 56]], [[50, 48, 48, 52, 53]], [[51, 48, 48, 48, 50]]]

theorem OMSExecutionReportFLEXPriceRequest.shape (record : OMSExecutionReportFLEXPriceRequest) : record.parts.map Part.tags = OMSExecutionReportFLEXPriceRequest.tags := rfl

def OMSExecutionReportFLEXPriceRequest.decode (tokens : List Token) : Option OMSExecutionReportFLEXPriceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let lastPx ← readOptional [51, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let referencePrice ← readRequired [50, 48, 48, 52, 53] tokens
  let refDealID ← readOptional [51, 48, 48, 48, 50] tokens
  pure { clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, maturityMonthYear, putOrCall, strikePrice, maturityDay, introducingBadgeID, referencePrice, refDealID }

theorem OMSExecutionReportFLEXPriceRequest.decode_agrees (record : OMSExecutionReportFLEXPriceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OMSExecutionReportFLEXPriceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OMSExecutionReportFLEXPriceRequest.decode tokens = some record := by
  have distinct : OMSExecutionReportFLEXPriceRequest.tags.flatten.Nodup := by decide +kernel
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
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have referencePrice := readRequired_part [50, 48, 48, 52, 53] record.referencePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have refDealID := readOptional_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [OMSExecutionReportFLEXPriceRequest.decode, clOrdID, lastPx, orderID, ordStatus, origClOrdID, symbol, maturityMonthYear, putOrCall, strikePrice, maturityDay, introducingBadgeID, referencePrice, refDealID, some_bind] <;> rfl

structure OMSExecutionReportAllocationRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  lastQty : Terminated 1  -- tag 32
  orderID : Terminated 1  -- tag 37
  ordStatus : Terminated 1  -- tag 39
  origClOrdID : Terminated 1  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  openClose : Option (Terminated 1)  -- tag 77
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Option (Terminated 1)  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  optionalData : Option (Terminated 1)  -- tag 526
  capStrategyID : Option (Terminated 1)  -- tag 7929
  introducingBadgeID : Terminated 1  -- tag 9448
  dealID : Terminated 1  -- tag 9483
  allocationFirmMPID : Option (Terminated 1)  -- tag 20022
  allocationFirmMMID : Option (Terminated 1)  -- tag 20023
  allocationFirmIntroducingBadgeID : Option (Terminated 1)  -- tag 20024
  refDealID : Terminated 1  -- tag 30002

def OMSExecutionReportAllocationRequest.parts (record : OMSExecutionReportAllocationRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 57] record.ordStatus,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [55, 55] record.openClose,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [53, 50, 54] record.optionalData,
   Part.optional [55, 57, 50, 57] record.capStrategyID,
   Part.required [57, 52, 52, 56] record.introducingBadgeID,
   Part.required [57, 52, 56, 51] record.dealID,
   Part.optional [50, 48, 48, 50, 50] record.allocationFirmMPID,
   Part.optional [50, 48, 48, 50, 51] record.allocationFirmMMID,
   Part.optional [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID,
   Part.required [51, 48, 48, 48, 50] record.refDealID]

def OMSExecutionReportAllocationRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[51, 50]], [[51, 55]], [[51, 57]], [[52, 49]], [[53, 52]], [[53, 53]], [[55, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [[52, 51, 57]], [[52, 52, 48]], [[53, 50, 54]], [[55, 57, 50, 57]], [[57, 52, 52, 56]], [[57, 52, 56, 51]], [[50, 48, 48, 50, 50]], [[50, 48, 48, 50, 51]], [[50, 48, 48, 50, 52]], [[51, 48, 48, 48, 50]]]

theorem OMSExecutionReportAllocationRequest.shape (record : OMSExecutionReportAllocationRequest) : record.parts.map Part.tags = OMSExecutionReportAllocationRequest.tags := rfl

def OMSExecutionReportAllocationRequest.decode (tokens : List Token) : Option OMSExecutionReportAllocationRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let openClose ← readOptional [55, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readOptional [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let optionalData ← readOptional [53, 50, 54] tokens
  let capStrategyID ← readOptional [55, 57, 50, 57] tokens
  let introducingBadgeID ← readRequired [57, 52, 52, 56] tokens
  let dealID ← readRequired [57, 52, 56, 51] tokens
  let allocationFirmMPID ← readOptional [50, 48, 48, 50, 50] tokens
  let allocationFirmMMID ← readOptional [50, 48, 48, 50, 51] tokens
  let allocationFirmIntroducingBadgeID ← readOptional [50, 48, 48, 50, 52] tokens
  let refDealID ← readRequired [51, 48, 48, 48, 50] tokens
  pure { account, clOrdID, lastQty, orderID, ordStatus, origClOrdID, side, symbol, openClose, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, clearingFirm, clearingAccount, optionalData, capStrategyID, introducingBadgeID, dealID, allocationFirmMPID, allocationFirmMMID, allocationFirmIntroducingBadgeID, refDealID }

theorem OMSExecutionReportAllocationRequest.decode_agrees (record : OMSExecutionReportAllocationRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OMSExecutionReportAllocationRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OMSExecutionReportAllocationRequest.decode tokens = some record := by
  have distinct : OMSExecutionReportAllocationRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have customerOrFirm := readOptional_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have optionalData := readOptional_part [53, 50, 54] record.optionalData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have capStrategyID := readOptional_part [55, 57, 50, 57] record.capStrategyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have introducingBadgeID := readRequired_part [57, 52, 52, 56] record.introducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have dealID := readRequired_part [57, 52, 56, 51] record.dealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have allocationFirmMPID := readOptional_part [50, 48, 48, 50, 50] record.allocationFirmMPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have allocationFirmMMID := readOptional_part [50, 48, 48, 50, 51] record.allocationFirmMMID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have allocationFirmIntroducingBadgeID := readOptional_part [50, 48, 48, 50, 52] record.allocationFirmIntroducingBadgeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have refDealID := readRequired_part [51, 48, 48, 48, 50] record.refDealID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  simp only [OMSExecutionReportAllocationRequest.decode, account, clOrdID, lastQty, orderID, ordStatus, origClOrdID, side, symbol, openClose, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, clearingFirm, clearingAccount, optionalData, capStrategyID, introducingBadgeID, dealID, allocationFirmMPID, allocationFirmMMID, allocationFirmIntroducingBadgeID, refDealID, some_bind] <;> rfl

inductive Message where
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | oMSExecutionReportTradeRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportTradeRequest)
  | oMSExecutionReportFLEXPriceRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportFLEXPriceRequest)
  | oMSExecutionReportAllocationRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportAllocationRequest)

def Message.tokens : Message → List Token
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegOrderCancelReplace header r0 => ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .oMSExecutionReportTradeRequest header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[84], by decide⟩] ++ r1.parts)
  | .oMSExecutionReportFLEXPriceRequest header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts)
  | .oMSExecutionReportAllocationRequest header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[75], by decide⟩] ++ r1.parts)

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
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [65, 66] then
        if known (Header.tags ++ NewOrderMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderMultileg.decode rest
          pure (.newOrderMultileg header r0)
        else none
      else if token.value.val = [65, 67] then
        if known (Header.tags ++ MultilegOrderCancelReplace.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MultilegOrderCancelReplace.decode rest
          pure (.multilegOrderCancelReplace header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [84] then
            if known (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportTradeRequest.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OMSExecutionReport.decode rest
              let r1 ← OMSExecutionReportTradeRequest.decode rest
              pure (.oMSExecutionReportTradeRequest header r0 r1)
            else none
          else if key.val = [85] then
            if known (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportFLEXPriceRequest.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OMSExecutionReport.decode rest
              let r1 ← OMSExecutionReportFLEXPriceRequest.decode rest
              pure (.oMSExecutionReportFLEXPriceRequest header r0 r1)
            else none
          else if key.val = [75] then
            if known (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportAllocationRequest.tags) rest then do
              let header ← Header.decode rest
              let r0 ← OMSExecutionReport.decode rest
              let r1 ← OMSExecutionReportAllocationRequest.decode rest
              pure (.oMSExecutionReportAllocationRequest header r0 r1)
            else none
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

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decode (Message.tokens (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decode (Message.tokens (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) rfl rfl (by decide +kernel))
  have c1 := MultilegOrderCancelReplace.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MultilegOrderCancelReplace.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplace.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_oMSExecutionReportTradeRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportTradeRequest) :
    Message.decode (Message.tokens (.oMSExecutionReportTradeRequest header r0 r1)) = some (.oMSExecutionReportTradeRequest header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[84], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportTradeRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OMSExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[84], by decide⟩] ++ r1.parts) (Header.tags) (OMSExecutionReport.tags) ([[[49, 53, 48]]] ++ OMSExecutionReportTradeRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[84], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[84], by decide⟩]) (r1.parts) (Header.tags ++ OMSExecutionReport.tags) ([[[49, 53, 48]]]) (OMSExecutionReportTradeRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OMSExecutionReportTradeRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[84], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]]) (OMSExecutionReportTradeRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[84], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportTradeRequest.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_oMSExecutionReportFLEXPriceRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportFLEXPriceRequest) :
    Message.decode (Message.tokens (.oMSExecutionReportFLEXPriceRequest header r0 r1)) = some (.oMSExecutionReportFLEXPriceRequest header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OMSExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags) (OMSExecutionReport.tags) ([[[49, 53, 48]]] ++ OMSExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[85], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) (Header.tags ++ OMSExecutionReport.tags) ([[[49, 53, 48]]]) (OMSExecutionReportFLEXPriceRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OMSExecutionReportFLEXPriceRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]]) (OMSExecutionReportFLEXPriceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportFLEXPriceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_oMSExecutionReportAllocationRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportAllocationRequest) :
    Message.decode (Message.tokens (.oMSExecutionReportAllocationRequest header r0 r1)) = some (.oMSExecutionReportAllocationRequest header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[75], by decide⟩] ++ r1.parts) ([]) (Header.tags) (OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportAllocationRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OMSExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[75], by decide⟩] ++ r1.parts) (Header.tags) (OMSExecutionReport.tags) ([[[49, 53, 48]]] ++ OMSExecutionReportAllocationRequest.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[75], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[75], by decide⟩]) (r1.parts) (Header.tags ++ OMSExecutionReport.tags) ([[[49, 53, 48]]]) (OMSExecutionReportAllocationRequest.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := OMSExecutionReportAllocationRequest.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[75], by decide⟩]) (r1.parts) ([]) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]]) (OMSExecutionReportAllocationRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[75], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportAllocationRequest.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | multilegOrderCancelReplace header r0 => exact Message.decode_multilegOrderCancelReplace header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | oMSExecutionReportTradeRequest header r0 r1 => exact Message.decode_oMSExecutionReportTradeRequest header r0 r1
  | oMSExecutionReportFLEXPriceRequest header r0 r1 => exact Message.decode_oMSExecutionReportFLEXPriceRequest header r0 r1
  | oMSExecutionReportAllocationRequest header r0 r1 => exact Message.decode_oMSExecutionReportAllocationRequest header r0 r1

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

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_newOrderMultileg (header : Header) (r0 : NewOrderMultileg) :
    Message.decodeBytes (Message.encode (.newOrderMultileg header r0)) = some (.newOrderMultileg header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderMultileg.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderMultileg header r0

theorem Message.decodeBytes_multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace) :
    Message.decodeBytes (Message.encode (.multilegOrderCancelReplace header r0)) = some (.multilegOrderCancelReplace header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MultilegOrderCancelReplace.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_multilegOrderCancelReplace header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_oMSExecutionReportTradeRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportTradeRequest) :
    Message.decodeBytes (Message.encode (.oMSExecutionReportTradeRequest header r0 r1)) = some (.oMSExecutionReportTradeRequest header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[84], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportTradeRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oMSExecutionReportTradeRequest header r0 r1

theorem Message.decodeBytes_oMSExecutionReportFLEXPriceRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportFLEXPriceRequest) :
    Message.decodeBytes (Message.encode (.oMSExecutionReportFLEXPriceRequest header r0 r1)) = some (.oMSExecutionReportFLEXPriceRequest header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[85], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportFLEXPriceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oMSExecutionReportFLEXPriceRequest header r0 r1

theorem Message.decodeBytes_oMSExecutionReportAllocationRequest (header : Header) (r0 : OMSExecutionReport) (r1 : OMSExecutionReportAllocationRequest) :
    Message.decodeBytes (Message.encode (.oMSExecutionReportAllocationRequest header r0 r1)) = some (.oMSExecutionReportAllocationRequest header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[75], by decide⟩] ++ r1.parts) (Header.tags ++ OMSExecutionReport.tags ++ [[[49, 53, 48]]] ++ OMSExecutionReportAllocationRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_oMSExecutionReportAllocationRequest header r0 r1

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | multilegOrderCancelReplace header r0 => exact Message.decodeBytes_multilegOrderCancelReplace header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | oMSExecutionReportTradeRequest header r0 r1 => exact Message.decodeBytes_oMSExecutionReportTradeRequest header r0 r1
  | oMSExecutionReportFLEXPriceRequest header r0 r1 => exact Message.decodeBytes_oMSExecutionReportFLEXPriceRequest header r0 r1
  | oMSExecutionReportAllocationRequest header r0 r1 => exact Message.decodeBytes_oMSExecutionReportAllocationRequest header r0 r1

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NyseArcaoptionsFloorbrokerFixV26Client
