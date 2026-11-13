import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Order Entry v12.1.12, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqMrxoptionsOrderentryFixV12112Client

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, origSendingTime }

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
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, origSendingTime, some_bind] <;> rfl

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  pure { encryptMethod, heartBtInt }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, some_bind] <;> rfl

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Terminated 1  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  displayWhen : Option (Terminated 1)  -- tag 1083
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  displayRange : Option (Terminated 1)  -- tag 8020
  auctionInst : Option (Terminated 1)  -- tag 8601
  specialOrdType : Option (Terminated 1)  -- tag 9202
  exposureFlag : Option (Terminated 1)  -- tag 9203
  routingInst : Option (Terminated 1)  -- tag 9303
  branchSeqNbr : Option (Terminated 1)  -- tag 9861

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.required [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [56, 54, 48, 49] record.auctionInst,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 51, 48, 51] record.routingInst,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[57, 57]], [[49, 49, 48]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 56, 51]], [[55, 57, 48, 49]], [[56, 48, 50, 48]], [[56, 54, 48, 49]], [[57, 50, 48, 50]], [[57, 50, 48, 51]], [[57, 51, 48, 51]], [[57, 56, 54, 49]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let auctionInst ← readOptional [56, 54, 48, 49] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let routingInst ← readOptional [57, 51, 48, 51] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  pure { account, clOrdID, execInst, handlInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, minQty, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, maturityDate, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, executingParticipantID, displayRange, auctionInst, specialOrdType, exposureFlag, routingInst, branchSeqNbr }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have auctionInst := readOptional_part [56, 54, 48, 49] record.auctionInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have routingInst := readOptional_part [57, 51, 48, 51] record.routingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, execInst, handlInst, orderQty, ordType, price, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, minQty, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, maturityDate, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, executingParticipantID, displayRange, auctionInst, specialOrdType, exposureFlag, routingInst, branchSeqNbr, some_bind] <;> rfl

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  transactTime : Terminated 1  -- tag 60
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  maturityDay : Option (Terminated 1)  -- tag 205
  maturityDate : Option (Terminated 1)  -- tag 541
  securityExchange : Option (Terminated 1)  -- tag 207
  noLegs : Option (Terminated 1)  -- tag 555
  legRefID : Option (Terminated 1)  -- tag 654
  legSymbol : Option (Terminated 1)  -- tag 600
  legCFICode : Option (Terminated 1)  -- tag 608
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legSide : Option (Terminated 1)  -- tag 624

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [53, 53, 53] record.noLegs,
   Part.optional [54, 53, 52] record.legRefID,
   Part.optional [54, 48, 48] record.legSymbol,
   Part.optional [54, 48, 56] record.legCFICode,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.optional [54, 50, 52] record.legSide]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 56]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 55]], [[53, 53, 53]], [[54, 53, 52]], [[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 52]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let noLegs ← readOptional [53, 53, 53] tokens
  let legRefID ← readOptional [54, 53, 52] tokens
  let legSymbol ← readOptional [54, 48, 48] tokens
  let legCFICode ← readOptional [54, 48, 56] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  pure { clOrdID, orderQty, origClOrdID, side, symbol, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate, securityExchange, noLegs, legRefID, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legSide }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noLegs := readOptional_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have legRefID := readOptional_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have legSymbol := readOptional_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have legCFICode := readOptional_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, orderQty, origClOrdID, side, symbol, transactTime, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate, securityExchange, noLegs, legRefID, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legSide, some_bind] <;> rfl

structure OrderCancelReplaceRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  openClose : Terminated 1  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  customerOrFirm : Terminated 1  -- tag 204
  maturityDay : Option (Terminated 1)  -- tag 205
  maturityDate : Option (Terminated 1)  -- tag 541
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  displayWhen : Option (Terminated 1)  -- tag 1083
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  displayRange : Option (Terminated 1)  -- tag 8020
  branchSeqNbr : Option (Terminated 1)  -- tag 9861

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.required [55, 55] record.openClose,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[57, 48, 52, 52]], [[57, 48, 52, 51]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[55, 55]], [[57, 57]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 52]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 56, 51]], [[49, 48, 57, 50]], [[56, 48, 50, 48]], [[57, 56, 54, 49]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  pure { account, clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, stepUpPrice, stepUpPriceType, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, maturityDate, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, displayRange, branchSeqNbr }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, account, clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, stepUpPrice, stepUpPriceType, side, symbol, text, timeInForce, transactTime, execBroker, openClose, stopPx, maxFloor, securityType, maturityMonthYear, putOrCall, strikePrice, customerOrFirm, maturityDay, maturityDate, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, displayRange, branchSeqNbr, some_bind] <;> rfl

structure NewOrderCross where
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  symbol : Terminated 1  -- tag 55
  timeInForce : Terminated 1  -- tag 59
  transactTime : Terminated 1  -- tag 60
  securityType : Terminated 1  -- tag 167
  effectiveTime : Option (Terminated 1)  -- tag 168
  maturityMonthYear : Terminated 1  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  securityExchange : Option (Terminated 1)  -- tag 207
  crossID : Terminated 1  -- tag 548
  crossType : Option (Terminated 1)  -- tag 549
  noSides : Terminated 1  -- tag 552
  side : Terminated 1  -- tag 54
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  customerOrFirm : Terminated 1  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  branchSeqNbr : Option (Terminated 1)  -- tag 9861
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  exposureFlag : Option (Terminated 1)  -- tag 9203
  brokerPct : Option (Terminated 1)  -- tag 9204
  underlyingPx : Option (Terminated 1)  -- tag 810
  underlyingQty : Option (Terminated 1)  -- tag 879
  priceDelta : Option (Terminated 1)  -- tag 9811

def NewOrderCross.parts (record : NewOrderCross) : List Part :=
  [Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [53, 53] record.symbol,
   Part.required [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [49, 54, 56] record.effectiveTime,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.required [53, 52, 56] record.crossID,
   Part.optional [53, 52, 57] record.crossType,
   Part.required [53, 53, 50] record.noSides,
   Part.required [53, 52] record.side,
   Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 50, 48, 52] record.brokerPct,
   Part.optional [56, 49, 48] record.underlyingPx,
   Part.optional [56, 55, 57] record.underlyingQty,
   Part.optional [57, 56, 49, 49] record.priceDelta]

def NewOrderCross.tags : List (List (List UInt8)) :=
  [[[49, 56]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 54, 55]], [[49, 54, 56]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 55]], [[53, 52, 56]], [[53, 52, 57]], [[53, 53, 50]], [[53, 52]], [[49]], [[49, 49]], [[53, 56]], [[55, 54]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[57, 56, 54, 49]], [[55, 57, 48, 49]], [[49, 48, 57, 50]], [[57, 48, 52, 52]], [[57, 48, 52, 51]], [[57, 50, 48, 51]], [[57, 50, 48, 52]], [[56, 49, 48]], [[56, 55, 57]], [[57, 56, 49, 49]]]

theorem NewOrderCross.shape (record : NewOrderCross) : record.parts.map Part.tags = NewOrderCross.tags := rfl

def NewOrderCross.decode (tokens : List Token) : Option NewOrderCross := do
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let effectiveTime ← readOptional [49, 54, 56] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let crossType ← readOptional [53, 52, 57] tokens
  let noSides ← readRequired [53, 53, 50] tokens
  let side ← readRequired [53, 52] tokens
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let brokerPct ← readOptional [57, 50, 48, 52] tokens
  let underlyingPx ← readOptional [56, 49, 48] tokens
  let underlyingQty ← readOptional [56, 55, 57] tokens
  let priceDelta ← readOptional [57, 56, 49, 49] tokens
  pure { execInst, orderQty, ordType, price, symbol, timeInForce, transactTime, securityType, effectiveTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate, securityExchange, crossID, crossType, noSides, side, account, clOrdID, text, execBroker, customerOrFirm, clearingFirm, clearingAccount, branchSeqNbr, executingParticipantID, priceProtectionScope, stepUpPrice, stepUpPriceType, exposureFlag, brokerPct, underlyingPx, underlyingQty, priceDelta }

theorem NewOrderCross.decode_agrees (record : NewOrderCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCross.decode tokens = some record := by
  have distinct : NewOrderCross.tags.flatten.Nodup := by decide +kernel
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have effectiveTime := readOptional_part [49, 54, 56] record.effectiveTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have crossType := readOptional_part [53, 52, 57] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have noSides := readRequired_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have brokerPct := readOptional_part [57, 50, 48, 52] record.brokerPct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have underlyingPx := readOptional_part [56, 49, 48] record.underlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have underlyingQty := readOptional_part [56, 55, 57] record.underlyingQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have priceDelta := readOptional_part [57, 56, 49, 49] record.priceDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [NewOrderCross.decode, execInst, orderQty, ordType, price, symbol, timeInForce, transactTime, securityType, effectiveTime, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate, securityExchange, crossID, crossType, noSides, side, account, clOrdID, text, execBroker, customerOrFirm, clearingFirm, clearingAccount, branchSeqNbr, executingParticipantID, priceProtectionScope, stepUpPrice, stepUpPriceType, exposureFlag, brokerPct, underlyingPx, underlyingQty, priceDelta, some_bind] <;> rfl

structure NewOrderMultileg where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  displayWhen : Option (Terminated 1)  -- tag 1083
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  displayRange : Option (Terminated 1)  -- tag 8020
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  specialOrdType : Option (Terminated 1)  -- tag 9202
  exposureFlag : Option (Terminated 1)  -- tag 9203
  branchSeqNbr : Option (Terminated 1)  -- tag 9861
  noLegs : Terminated 1  -- tag 555
  legRefID : Terminated 1  -- tag 654
  legPositionEffect : Option (Terminated 1)  -- tag 564
  legSymbol : Terminated 1  -- tag 600
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  contraLegPositionEffect : Option (Terminated 1)  -- tag 9564
  contraSideShortSell : Option (Terminated 1)  -- tag 9624

def NewOrderMultileg.parts (record : NewOrderMultileg) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.optional [57, 50, 48, 50] record.specialOrdType,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 53, 52] record.legRefID,
   Part.optional [53, 54, 52] record.legPositionEffect,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 56] record.legCFICode,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [57, 53, 54, 52] record.contraLegPositionEffect,
   Part.optional [57, 54, 50, 52] record.contraSideShortSell]

def NewOrderMultileg.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[49, 49, 48]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 56, 51]], [[49, 48, 57, 50]], [[55, 57, 48, 49]], [[56, 48, 50, 48]], [[57, 48, 55, 54]], [[57, 50, 48, 50]], [[57, 50, 48, 51]], [[57, 56, 54, 49]], [[53, 53, 53]], [[54, 53, 52]], [[53, 54, 52]], [[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[57, 53, 54, 52]], [[57, 54, 50, 52]]]

theorem NewOrderMultileg.shape (record : NewOrderMultileg) : record.parts.map Part.tags = NewOrderMultileg.tags := rfl

def NewOrderMultileg.decode (tokens : List Token) : Option NewOrderMultileg := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let specialOrdType ← readOptional [57, 50, 48, 50] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  let legPositionEffect ← readOptional [53, 54, 52] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let contraLegPositionEffect ← readOptional [57, 53, 54, 52] tokens
  let contraSideShortSell ← readOptional [57, 54, 50, 52] tokens
  pure { account, clOrdID, execInst, handlInst, orderQty, ordType, price, text, timeInForce, transactTime, execBroker, minQty, maxFloor, securityType, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, executingParticipantID, displayRange, stockLegGiveUp, specialOrdType, exposureFlag, branchSeqNbr, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell }

theorem NewOrderMultileg.decode_agrees (record : NewOrderMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderMultileg.decode tokens = some record := by
  have distinct : NewOrderMultileg.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have specialOrdType := readOptional_part [57, 50, 48, 50] record.specialOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have legPositionEffect := readOptional_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have contraLegPositionEffect := readOptional_part [57, 53, 54, 52] record.contraLegPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have contraSideShortSell := readOptional_part [57, 54, 50, 52] record.contraSideShortSell tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  simp only [NewOrderMultileg.decode, account, clOrdID, execInst, handlInst, orderQty, ordType, price, text, timeInForce, transactTime, execBroker, minQty, maxFloor, securityType, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, executingParticipantID, displayRange, stockLegGiveUp, specialOrdType, exposureFlag, branchSeqNbr, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell, some_bind] <;> rfl

structure MultilegOrderCancelReplace where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Terminated 1  -- tag 44
  text : Option (Terminated 1)  -- tag 58
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Terminated 1  -- tag 167
  customerOrFirm : Terminated 1  -- tag 204
  securityExchange : Option (Terminated 1)  -- tag 207
  expireDate : Option (Terminated 1)  -- tag 432
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  displayWhen : Option (Terminated 1)  -- tag 1083
  priceProtectionScope : Option (Terminated 1)  -- tag 1092
  displayRange : Option (Terminated 1)  -- tag 8020
  exposureFlag : Option (Terminated 1)  -- tag 9203
  branchSeqNbr : Option (Terminated 1)  -- tag 9861
  noLegs : Terminated 1  -- tag 555
  legRefID : Terminated 1  -- tag 654
  legPositionEffect : Option (Terminated 1)  -- tag 564
  legSymbol : Terminated 1  -- tag 600
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624

def MultilegOrderCancelReplace.parts (record : MultilegOrderCancelReplace) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.required [52, 52] record.price,
   Part.optional [53, 56] record.text,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.required [49, 54, 55] record.securityType,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [49, 48, 56, 51] record.displayWhen,
   Part.optional [49, 48, 57, 50] record.priceProtectionScope,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 53, 52] record.legRefID,
   Part.optional [53, 54, 52] record.legPositionEffect,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 56] record.legCFICode,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide]

def MultilegOrderCancelReplace.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 56]], [[57, 48, 52, 52]], [[57, 48, 52, 51]], [[53, 57]], [[54, 48]], [[55, 54]], [[49, 49, 48]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 52]], [[50, 48, 55]], [[52, 51, 50]], [[52, 51, 57]], [[52, 52, 48]], [[49, 48, 56, 51]], [[49, 48, 57, 50]], [[56, 48, 50, 48]], [[57, 50, 48, 51]], [[57, 56, 54, 49]], [[53, 53, 53]], [[54, 53, 52]], [[53, 54, 52]], [[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]]]

theorem MultilegOrderCancelReplace.shape (record : MultilegOrderCancelReplace) : record.parts.map Part.tags = MultilegOrderCancelReplace.tags := rfl

def MultilegOrderCancelReplace.decode (tokens : List Token) : Option MultilegOrderCancelReplace := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readRequired [52, 52] tokens
  let text ← readOptional [53, 56] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let displayWhen ← readOptional [49, 48, 56, 51] tokens
  let priceProtectionScope ← readOptional [49, 48, 57, 50] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  let legPositionEffect ← readOptional [53, 54, 52] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  pure { account, clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, text, stepUpPrice, stepUpPriceType, timeInForce, transactTime, execBroker, minQty, maxFloor, securityType, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, displayRange, exposureFlag, branchSeqNbr, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide }

theorem MultilegOrderCancelReplace.decode_agrees (record : MultilegOrderCancelReplace) (tokens : List Token)
    (agrees : ∀ tags ∈ MultilegOrderCancelReplace.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MultilegOrderCancelReplace.decode tokens = some record := by
  have distinct : MultilegOrderCancelReplace.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have displayWhen := readOptional_part [49, 48, 56, 51] record.displayWhen tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have priceProtectionScope := readOptional_part [49, 48, 57, 50] record.priceProtectionScope tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have legPositionEffect := readOptional_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [MultilegOrderCancelReplace.decode, account, clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, text, stepUpPrice, stepUpPriceType, timeInForce, transactTime, execBroker, minQty, maxFloor, securityType, customerOrFirm, securityExchange, expireDate, clearingFirm, clearingAccount, displayWhen, priceProtectionScope, displayRange, exposureFlag, branchSeqNbr, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, some_bind] <;> rfl

structure NewOrderCrossMultileg where
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  transactTime : Terminated 1  -- tag 60
  exDestination : Option (Terminated 1)  -- tag 100
  securityExchange : Terminated 1  -- tag 207
  crossID : Terminated 1  -- tag 548
  crossType : Terminated 1  -- tag 549
  noSides : Terminated 1  -- tag 552
  clOrdID : Terminated 1  -- tag 11
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  execBroker : Option (Terminated 1)  -- tag 76
  customerOrFirm : Terminated 1  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  branchSeqNbr : Option (Terminated 1)  -- tag 9861
  executingParticipantID : Option (Terminated 1)  -- tag 7901
  stepUpPrice : Option (Terminated 1)  -- tag 9044
  stepUpPriceType : Option (Terminated 1)  -- tag 9043
  exposureFlag : Option (Terminated 1)  -- tag 9203
  brokerPct : Option (Terminated 1)  -- tag 9204
  underlyingPx : Option (Terminated 1)  -- tag 810
  underlyingQty : Option (Terminated 1)  -- tag 879
  priceDelta : Option (Terminated 1)  -- tag 9811
  noLegs : Terminated 1  -- tag 555
  legRefID : Terminated 1  -- tag 654
  legPositionEffect : Option (Terminated 1)  -- tag 564
  legSymbol : Terminated 1  -- tag 600
  legCFICode : Terminated 1  -- tag 608
  legMaturityDate : Option (Terminated 1)  -- tag 611
  legStrikePrice : Option (Terminated 1)  -- tag 612
  legRatioQty : Terminated 1  -- tag 623
  legSide : Terminated 1  -- tag 624
  contraLegPositionEffect : Option (Terminated 1)  -- tag 9564
  contraSideShortSell : Option (Terminated 1)  -- tag 9624

def NewOrderCrossMultileg.parts (record : NewOrderCrossMultileg) : List Part :=
  [Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 48] record.exDestination,
   Part.required [50, 48, 55] record.securityExchange,
   Part.required [53, 52, 56] record.crossID,
   Part.required [53, 52, 57] record.crossType,
   Part.required [53, 53, 50] record.noSides,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54] record.execBroker,
   Part.required [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr,
   Part.optional [55, 57, 48, 49] record.executingParticipantID,
   Part.optional [57, 48, 52, 52] record.stepUpPrice,
   Part.optional [57, 48, 52, 51] record.stepUpPriceType,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 50, 48, 52] record.brokerPct,
   Part.optional [56, 49, 48] record.underlyingPx,
   Part.optional [56, 55, 57] record.underlyingQty,
   Part.optional [57, 56, 49, 49] record.priceDelta,
   Part.required [53, 53, 53] record.noLegs,
   Part.required [54, 53, 52] record.legRefID,
   Part.optional [53, 54, 52] record.legPositionEffect,
   Part.required [54, 48, 48] record.legSymbol,
   Part.required [54, 48, 56] record.legCFICode,
   Part.optional [54, 49, 49] record.legMaturityDate,
   Part.optional [54, 49, 50] record.legStrikePrice,
   Part.required [54, 50, 51] record.legRatioQty,
   Part.required [54, 50, 52] record.legSide,
   Part.optional [57, 53, 54, 52] record.contraLegPositionEffect,
   Part.optional [57, 54, 50, 52] record.contraSideShortSell]

def NewOrderCrossMultileg.tags : List (List (List UInt8)) :=
  [[[51, 56]], [[52, 48]], [[52, 52]], [[54, 48]], [[49, 48, 48]], [[50, 48, 55]], [[53, 52, 56]], [[53, 52, 57]], [[53, 53, 50]], [[49, 49]], [[49]], [[53, 56]], [[55, 54]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[57, 48, 55, 54]], [[57, 56, 54, 49]], [[55, 57, 48, 49]], [[57, 48, 52, 52]], [[57, 48, 52, 51]], [[57, 50, 48, 51]], [[57, 50, 48, 52]], [[56, 49, 48]], [[56, 55, 57]], [[57, 56, 49, 49]], [[53, 53, 53]], [[54, 53, 52]], [[53, 54, 52]], [[54, 48, 48]], [[54, 48, 56]], [[54, 49, 49]], [[54, 49, 50]], [[54, 50, 51]], [[54, 50, 52]], [[57, 53, 54, 52]], [[57, 54, 50, 52]]]

theorem NewOrderCrossMultileg.shape (record : NewOrderCrossMultileg) : record.parts.map Part.tags = NewOrderCrossMultileg.tags := rfl

def NewOrderCrossMultileg.decode (tokens : List Token) : Option NewOrderCrossMultileg := do
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let securityExchange ← readRequired [50, 48, 55] tokens
  let crossID ← readRequired [53, 52, 56] tokens
  let crossType ← readRequired [53, 52, 57] tokens
  let noSides ← readRequired [53, 53, 50] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readOptional [55, 54] tokens
  let customerOrFirm ← readRequired [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let executingParticipantID ← readOptional [55, 57, 48, 49] tokens
  let stepUpPrice ← readOptional [57, 48, 52, 52] tokens
  let stepUpPriceType ← readOptional [57, 48, 52, 51] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let brokerPct ← readOptional [57, 50, 48, 52] tokens
  let underlyingPx ← readOptional [56, 49, 48] tokens
  let underlyingQty ← readOptional [56, 55, 57] tokens
  let priceDelta ← readOptional [57, 56, 49, 49] tokens
  let noLegs ← readRequired [53, 53, 53] tokens
  let legRefID ← readRequired [54, 53, 52] tokens
  let legPositionEffect ← readOptional [53, 54, 52] tokens
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legCFICode ← readRequired [54, 48, 56] tokens
  let legMaturityDate ← readOptional [54, 49, 49] tokens
  let legStrikePrice ← readOptional [54, 49, 50] tokens
  let legRatioQty ← readRequired [54, 50, 51] tokens
  let legSide ← readRequired [54, 50, 52] tokens
  let contraLegPositionEffect ← readOptional [57, 53, 54, 52] tokens
  let contraSideShortSell ← readOptional [57, 54, 50, 52] tokens
  pure { orderQty, ordType, price, transactTime, exDestination, securityExchange, crossID, crossType, noSides, clOrdID, account, text, execBroker, customerOrFirm, clearingFirm, clearingAccount, stockLegGiveUp, branchSeqNbr, executingParticipantID, stepUpPrice, stepUpPriceType, exposureFlag, brokerPct, underlyingPx, underlyingQty, priceDelta, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell }

theorem NewOrderCrossMultileg.decode_agrees (record : NewOrderCrossMultileg) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderCrossMultileg.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderCrossMultileg.decode tokens = some record := by
  have distinct : NewOrderCrossMultileg.tags.flatten.Nodup := by decide +kernel
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityExchange := readRequired_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have crossID := readRequired_part [53, 52, 56] record.crossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have crossType := readRequired_part [53, 52, 57] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noSides := readRequired_part [53, 53, 50] record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have customerOrFirm := readRequired_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have executingParticipantID := readOptional_part [55, 57, 48, 49] record.executingParticipantID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have stepUpPrice := readOptional_part [57, 48, 52, 52] record.stepUpPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have stepUpPriceType := readOptional_part [57, 48, 52, 51] record.stepUpPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have brokerPct := readOptional_part [57, 50, 48, 52] record.brokerPct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have underlyingPx := readOptional_part [56, 49, 48] record.underlyingPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have underlyingQty := readOptional_part [56, 55, 57] record.underlyingQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have priceDelta := readOptional_part [57, 56, 49, 49] record.priceDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have noLegs := readRequired_part [53, 53, 53] record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have legRefID := readRequired_part [54, 53, 52] record.legRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have legPositionEffect := readOptional_part [53, 54, 52] record.legPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have legCFICode := readRequired_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have legMaturityDate := readOptional_part [54, 49, 49] record.legMaturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have legStrikePrice := readOptional_part [54, 49, 50] record.legStrikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have legRatioQty := readRequired_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have legSide := readRequired_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have contraLegPositionEffect := readOptional_part [57, 53, 54, 52] record.contraLegPositionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have contraSideShortSell := readOptional_part [57, 54, 50, 52] record.contraSideShortSell tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  simp only [NewOrderCrossMultileg.decode, orderQty, ordType, price, transactTime, exDestination, securityExchange, crossID, crossType, noSides, clOrdID, account, text, execBroker, customerOrFirm, clearingFirm, clearingAccount, stockLegGiveUp, branchSeqNbr, executingParticipantID, stepUpPrice, stepUpPriceType, exposureFlag, brokerPct, underlyingPx, underlyingQty, priceDelta, noLegs, legRefID, legPositionEffect, legSymbol, legCFICode, legMaturityDate, legStrikePrice, legRatioQty, legSide, contraLegPositionEffect, contraSideShortSell, some_bind] <;> rfl

structure Allocation where
  iDSource : Option (Terminated 1)  -- tag 22
  securityID : Option (Terminated 1)  -- tag 48
  shares : Terminated 1  -- tag 53
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Option (Terminated 1)  -- tag 60
  allocID : Terminated 1  -- tag 70
  allocTransType : Terminated 1  -- tag 71
  noOrders : Terminated 1  -- tag 73
  clOrdID : Terminated 1  -- tag 11
  tradeDate : Option (Terminated 1)  -- tag 75
  noAllocs : Terminated 1  -- tag 78
  allocShares : Terminated 1  -- tag 80
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  execBroker : Terminated 1  -- tag 76
  openClose : Option (Terminated 1)  -- tag 77
  customerOrFirm : Option (Terminated 1)  -- tag 204
  clearingFirm : Option (Terminated 1)  -- tag 439
  clearingAccount : Option (Terminated 1)  -- tag 440
  branchSeqNbr : Option (Terminated 1)  -- tag 9861
  stockLegGiveUp : Option (Terminated 1)  -- tag 9076
  noExecs : Terminated 1  -- tag 124
  execID : Terminated 1  -- tag 17
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  maturityDay : Option (Terminated 1)  -- tag 205
  maturityDate : Option (Terminated 1)  -- tag 541

def Allocation.parts (record : Allocation) : List Part :=
  [Part.optional [50, 50] record.iDSource,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 51] record.shares,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 48] record.transactTime,
   Part.required [55, 48] record.allocID,
   Part.required [55, 49] record.allocTransType,
   Part.required [55, 51] record.noOrders,
   Part.required [49, 49] record.clOrdID,
   Part.optional [55, 53] record.tradeDate,
   Part.required [55, 56] record.noAllocs,
   Part.required [56, 48] record.allocShares,
   Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.required [55, 54] record.execBroker,
   Part.optional [55, 55] record.openClose,
   Part.optional [50, 48, 52] record.customerOrFirm,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [57, 56, 54, 49] record.branchSeqNbr,
   Part.optional [57, 48, 55, 54] record.stockLegGiveUp,
   Part.required [49, 50, 52] record.noExecs,
   Part.required [49, 55] record.execID,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [50, 48, 53] record.maturityDay,
   Part.optional [53, 52, 49] record.maturityDate]

def Allocation.tags : List (List (List UInt8)) :=
  [[[50, 50]], [[52, 56]], [[53, 51]], [[53, 52]], [[53, 53]], [[54, 48]], [[55, 48]], [[55, 49]], [[55, 51]], [[49, 49]], [[55, 53]], [[55, 56]], [[56, 48]], [[49]], [[53, 56]], [[55, 54]], [[55, 55]], [[50, 48, 52]], [[52, 51, 57]], [[52, 52, 48]], [[57, 56, 54, 49]], [[57, 48, 55, 54]], [[49, 50, 52]], [[49, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[50, 48, 53]], [[53, 52, 49]]]

theorem Allocation.shape (record : Allocation) : record.parts.map Part.tags = Allocation.tags := rfl

def Allocation.decode (tokens : List Token) : Option Allocation := do
  let iDSource ← readOptional [50, 50] tokens
  let securityID ← readOptional [52, 56] tokens
  let shares ← readRequired [53, 51] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let allocID ← readRequired [55, 48] tokens
  let allocTransType ← readRequired [55, 49] tokens
  let noOrders ← readRequired [55, 51] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let tradeDate ← readOptional [55, 53] tokens
  let noAllocs ← readRequired [55, 56] tokens
  let allocShares ← readRequired [56, 48] tokens
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let execBroker ← readRequired [55, 54] tokens
  let openClose ← readOptional [55, 55] tokens
  let customerOrFirm ← readOptional [50, 48, 52] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let branchSeqNbr ← readOptional [57, 56, 54, 49] tokens
  let stockLegGiveUp ← readOptional [57, 48, 55, 54] tokens
  let noExecs ← readRequired [49, 50, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let maturityDay ← readOptional [50, 48, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  pure { iDSource, securityID, shares, side, symbol, transactTime, allocID, allocTransType, noOrders, clOrdID, tradeDate, noAllocs, allocShares, account, text, execBroker, openClose, customerOrFirm, clearingFirm, clearingAccount, branchSeqNbr, stockLegGiveUp, noExecs, execID, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate }

theorem Allocation.decode_agrees (record : Allocation) (tokens : List Token)
    (agrees : ∀ tags ∈ Allocation.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Allocation.decode tokens = some record := by
  have distinct : Allocation.tags.flatten.Nodup := by decide +kernel
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have shares := readRequired_part [53, 51] record.shares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have allocID := readRequired_part [55, 48] record.allocID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have allocTransType := readRequired_part [55, 49] record.allocTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noOrders := readRequired_part [55, 51] record.noOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noAllocs := readRequired_part [55, 56] record.noAllocs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have allocShares := readRequired_part [56, 48] record.allocShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execBroker := readRequired_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have openClose := readOptional_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have customerOrFirm := readOptional_part [50, 48, 52] record.customerOrFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have branchSeqNbr := readOptional_part [57, 56, 54, 49] record.branchSeqNbr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have stockLegGiveUp := readOptional_part [57, 48, 55, 54] record.stockLegGiveUp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noExecs := readRequired_part [49, 50, 52] record.noExecs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have maturityDay := readOptional_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  simp only [Allocation.decode, iDSource, securityID, shares, side, symbol, transactTime, allocID, allocTransType, noOrders, clOrdID, tradeDate, noAllocs, allocShares, account, text, execBroker, openClose, customerOrFirm, clearingFirm, clearingAccount, branchSeqNbr, stockLegGiveUp, noExecs, execID, securityType, maturityMonthYear, putOrCall, strikePrice, maturityDay, maturityDate, some_bind] <;> rfl

structure MemberKillSwitch where
  entitlementRequestID : Terminated 1  -- tag 1770
  noPartyEntitlements : Terminated 1  -- tag 1772
  listUpdateAction : Terminated 1  -- tag 1324
  noPartyDetails : Terminated 1  -- tag 1671
  partyDetailID : Terminated 1  -- tag 1691
  partyDetailRole : Terminated 1  -- tag 1693

def MemberKillSwitch.parts (record : MemberKillSwitch) : List Part :=
  [Part.required [49, 55, 55, 48] record.entitlementRequestID,
   Part.required [49, 55, 55, 50] record.noPartyEntitlements,
   Part.required [49, 51, 50, 52] record.listUpdateAction,
   Part.required [49, 54, 55, 49] record.noPartyDetails,
   Part.required [49, 54, 57, 49] record.partyDetailID,
   Part.required [49, 54, 57, 51] record.partyDetailRole]

def MemberKillSwitch.tags : List (List (List UInt8)) :=
  [[[49, 55, 55, 48]], [[49, 55, 55, 50]], [[49, 51, 50, 52]], [[49, 54, 55, 49]], [[49, 54, 57, 49]], [[49, 54, 57, 51]]]

theorem MemberKillSwitch.shape (record : MemberKillSwitch) : record.parts.map Part.tags = MemberKillSwitch.tags := rfl

def MemberKillSwitch.decode (tokens : List Token) : Option MemberKillSwitch := do
  let entitlementRequestID ← readRequired [49, 55, 55, 48] tokens
  let noPartyEntitlements ← readRequired [49, 55, 55, 50] tokens
  let listUpdateAction ← readRequired [49, 51, 50, 52] tokens
  let noPartyDetails ← readRequired [49, 54, 55, 49] tokens
  let partyDetailID ← readRequired [49, 54, 57, 49] tokens
  let partyDetailRole ← readRequired [49, 54, 57, 51] tokens
  pure { entitlementRequestID, noPartyEntitlements, listUpdateAction, noPartyDetails, partyDetailID, partyDetailRole }

theorem MemberKillSwitch.decode_agrees (record : MemberKillSwitch) (tokens : List Token)
    (agrees : ∀ tags ∈ MemberKillSwitch.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MemberKillSwitch.decode tokens = some record := by
  have distinct : MemberKillSwitch.tags.flatten.Nodup := by decide +kernel
  have entitlementRequestID := readRequired_part [49, 55, 55, 48] record.entitlementRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noPartyEntitlements := readRequired_part [49, 55, 55, 50] record.noPartyEntitlements tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have listUpdateAction := readRequired_part [49, 51, 50, 52] record.listUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyDetails := readRequired_part [49, 54, 55, 49] record.noPartyDetails tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyDetailID := readRequired_part [49, 54, 57, 49] record.partyDetailID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyDetailRole := readRequired_part [49, 54, 57, 51] record.partyDetailRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [MemberKillSwitch.decode, entitlementRequestID, noPartyEntitlements, listUpdateAction, noPartyDetails, partyDetailID, partyDetailRole, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | newOrderCross (header : Header) (r0 : NewOrderCross)
  | newOrderMultileg (header : Header) (r0 : NewOrderMultileg)
  | multilegOrderCancelReplace (header : Header) (r0 : MultilegOrderCancelReplace)
  | newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg)
  | allocation (header : Header) (r0 : Allocation)
  | memberKillSwitch (header : Header) (r0 : MemberKillSwitch)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCross header r0 => ⟨[51, 53], ⟨[115], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderMultileg header r0 => ⟨[51, 53], ⟨[65, 66], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .multilegOrderCancelReplace header r0 => ⟨[51, 53], ⟨[65, 67], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderCrossMultileg header r0 => ⟨[51, 53], ⟨[65, 115], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .allocation header r0 => ⟨[51, 53], ⟨[74], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .memberKillSwitch header r0 => ⟨[51, 53], ⟨[85, 68, 65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value.val = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value.val = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value.val = [115] then
        if known (Header.tags ++ NewOrderCross.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCross.decode rest
          pure (.newOrderCross header r0)
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
      else if token.value.val = [65, 115] then
        if known (Header.tags ++ NewOrderCrossMultileg.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderCrossMultileg.decode rest
          pure (.newOrderCrossMultileg header r0)
        else none
      else if token.value.val = [74] then
        if known (Header.tags ++ Allocation.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Allocation.decode rest
          pure (.allocation header r0)
        else none
      else if token.value.val = [85, 68, 65] then
        if known (Header.tags ++ MemberKillSwitch.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MemberKillSwitch.decode rest
          pure (.memberKillSwitch header r0)
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

theorem Message.decode_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decode (Message.tokens (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCross.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags) rfl
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

theorem Message.decode_newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg) :
    Message.decode (Message.tokens (.newOrderCrossMultileg header r0)) = some (.newOrderCrossMultileg header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCrossMultileg.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderCrossMultileg.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderCrossMultileg.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderCrossMultileg.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_allocation (header : Header) (r0 : Allocation) :
    Message.decode (Message.tokens (.allocation header r0)) = some (.allocation header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Allocation.tags) rfl rfl (by decide +kernel))
  have c1 := Allocation.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Allocation.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Allocation.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_memberKillSwitch (header : Header) (r0 : MemberKillSwitch) :
    Message.decode (Message.tokens (.memberKillSwitch header r0)) = some (.memberKillSwitch header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitch.tags) rfl rfl (by decide +kernel))
  have c1 := MemberKillSwitch.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MemberKillSwitch.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitch.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | newOrderCross header r0 => exact Message.decode_newOrderCross header r0
  | newOrderMultileg header r0 => exact Message.decode_newOrderMultileg header r0
  | multilegOrderCancelReplace header r0 => exact Message.decode_multilegOrderCancelReplace header r0
  | newOrderCrossMultileg header r0 => exact Message.decode_newOrderCrossMultileg header r0
  | allocation header r0 => exact Message.decode_allocation header r0
  | memberKillSwitch header r0 => exact Message.decode_memberKillSwitch header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logon.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[68], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_newOrderCross (header : Header) (r0 : NewOrderCross) :
    Message.decodeBytes (Message.encode (.newOrderCross header r0)) = some (.newOrderCross header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[115], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderCross.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCross header r0

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

theorem Message.decodeBytes_newOrderCrossMultileg (header : Header) (r0 : NewOrderCrossMultileg) :
    Message.decodeBytes (Message.encode (.newOrderCrossMultileg header r0)) = some (.newOrderCrossMultileg header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[65, 115], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ NewOrderCrossMultileg.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderCrossMultileg header r0

theorem Message.decodeBytes_allocation (header : Header) (r0 : Allocation) :
    Message.decodeBytes (Message.encode (.allocation header r0)) = some (.allocation header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[74], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Allocation.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_allocation header r0

theorem Message.decodeBytes_memberKillSwitch (header : Header) (r0 : MemberKillSwitch) :
    Message.decodeBytes (Message.encode (.memberKillSwitch header r0)) = some (.memberKillSwitch header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85, 68, 65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ MemberKillSwitch.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_memberKillSwitch header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | newOrderCross header r0 => exact Message.decodeBytes_newOrderCross header r0
  | newOrderMultileg header r0 => exact Message.decodeBytes_newOrderMultileg header r0
  | multilegOrderCancelReplace header r0 => exact Message.decodeBytes_multilegOrderCancelReplace header r0
  | newOrderCrossMultileg header r0 => exact Message.decodeBytes_newOrderCrossMultileg header r0
  | allocation header r0 => exact Message.decodeBytes_allocation header r0
  | memberKillSwitch header r0 => exact Message.decodeBytes_memberKillSwitch header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqMrxoptionsOrderentryFixV12112Client
