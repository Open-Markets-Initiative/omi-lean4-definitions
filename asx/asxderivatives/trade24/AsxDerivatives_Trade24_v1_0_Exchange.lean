import Wire

/-!
# Australian Securities Exchange Trade24 v1.0, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.AsxAsxderivativesTrade24FixV10Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

structure Logon where
  heartBtInt : Terminated 1  -- tag 108
  rawDataLength : Option (Terminated 1)  -- tag 95
  rawData : Option (Terminated 1)  -- tag 96

def Logon.parts (record : Logon) : List Part :=
  [Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [57, 53] record.rawDataLength,
   Part.optional [57, 54] record.rawData]

def Logon.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]], [[57, 53]], [[57, 54]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawDataLength ← readOptional [57, 53] tokens
  let rawData ← readOptional [57, 54] tokens
  pure { heartBtInt, rawDataLength, rawData }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rawDataLength := readOptional_part [57, 53] record.rawDataLength tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rawData := readOptional_part [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [Logon.decode, heartBtInt, rawDataLength, rawData, some_bind] <;> rfl

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

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, text }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, some_bind] <;> rfl

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

structure UserMessage where
  userMsgCat : Terminated 1  -- tag 5001
  exDestination : Option (Terminated 1)  -- tag 100
  symbol : Option (Terminated 1)  -- tag 55
  currency : Option (Terminated 1)  -- tag 5004
  fOBIndicator : Option (Terminated 1)  -- tag 5021
  text : Option (Terminated 1)  -- tag 58
  lastMessage : Option (Terminated 1)  -- tag 5003
  instrmntIndicator : Option (Terminated 1)  -- tag 5002
  monthYear : Option (Terminated 1)  -- tag 5009
  tickIncrement : Option (Terminated 1)  -- tag 5005
  underlyingFut : Option (Terminated 1)  -- tag 5010
  fractionalIndicator : Option (Terminated 1)  -- tag 5054
  referenceNo : Option (Terminated 1)  -- tag 5036
  filterType : Option (Terminated 1)  -- tag 5033
  interSpreadsFlag : Option (Terminated 1)  -- tag 5034
  interSprdRatio : Option (Terminated 1)  -- tag 5028
  optionsStrikeP : Option (Terminated 1)  -- tag 5013
  marketStatus : Option (Terminated 1)  -- tag 5014
  settlementPrice : Option (Terminated 1)  -- tag 5017
  volatility : Option (Terminated 1)  -- tag 5018
  openPrice : Option (Terminated 1)  -- tag 5019
  closePrice : Option (Terminated 1)  -- tag 5020
  highTradePrice : Option (Terminated 1)  -- tag 5016
  lowTradePrice : Option (Terminated 1)  -- tag 5015
  askPrice : Option (Terminated 1)  -- tag 5022
  askVolume : Option (Terminated 1)  -- tag 5023
  bidPrice : Option (Terminated 1)  -- tag 5024
  bidVolume : Option (Terminated 1)  -- tag 5025
  lastTradedPrice : Option (Terminated 1)  -- tag 5026
  lastTradedVolume : Option (Terminated 1)  -- tag 5011
  totalTradedVolume : Option (Terminated 1)  -- tag 5055
  interimSettlement : Option (Terminated 1)  -- tag 5056
  lastBuyer : Option (Terminated 1)  -- tag 5031
  lastSeller : Option (Terminated 1)  -- tag 5032
  impliedPrice25 : Option (Terminated 1)  -- tag 5057
  userMsgCatReq : Option (Terminated 1)  -- tag 5053
  sendMsgType : Option (Terminated 1)  -- tag 5048
  sendMsgUserId : Option (Terminated 1)  -- tag 5049
  sendMsgText : Option (Terminated 1)  -- tag 5050
  quoteVolume : Option (Terminated 1)  -- tag 5051
  quoteFirm : Option (Terminated 1)  -- tag 5052

def UserMessage.parts (record : UserMessage) : List Part :=
  [Part.required [53, 48, 48, 49] record.userMsgCat,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [53, 53] record.symbol,
   Part.optional [53, 48, 48, 52] record.currency,
   Part.optional [53, 48, 50, 49] record.fOBIndicator,
   Part.optional [53, 56] record.text,
   Part.optional [53, 48, 48, 51] record.lastMessage,
   Part.optional [53, 48, 48, 50] record.instrmntIndicator,
   Part.optional [53, 48, 48, 57] record.monthYear,
   Part.optional [53, 48, 48, 53] record.tickIncrement,
   Part.optional [53, 48, 49, 48] record.underlyingFut,
   Part.optional [53, 48, 53, 52] record.fractionalIndicator,
   Part.optional [53, 48, 51, 54] record.referenceNo,
   Part.optional [53, 48, 51, 51] record.filterType,
   Part.optional [53, 48, 51, 52] record.interSpreadsFlag,
   Part.optional [53, 48, 50, 56] record.interSprdRatio,
   Part.optional [53, 48, 49, 51] record.optionsStrikeP,
   Part.optional [53, 48, 49, 52] record.marketStatus,
   Part.optional [53, 48, 49, 55] record.settlementPrice,
   Part.optional [53, 48, 49, 56] record.volatility,
   Part.optional [53, 48, 49, 57] record.openPrice,
   Part.optional [53, 48, 50, 48] record.closePrice,
   Part.optional [53, 48, 49, 54] record.highTradePrice,
   Part.optional [53, 48, 49, 53] record.lowTradePrice,
   Part.optional [53, 48, 50, 50] record.askPrice,
   Part.optional [53, 48, 50, 51] record.askVolume,
   Part.optional [53, 48, 50, 52] record.bidPrice,
   Part.optional [53, 48, 50, 53] record.bidVolume,
   Part.optional [53, 48, 50, 54] record.lastTradedPrice,
   Part.optional [53, 48, 49, 49] record.lastTradedVolume,
   Part.optional [53, 48, 53, 53] record.totalTradedVolume,
   Part.optional [53, 48, 53, 54] record.interimSettlement,
   Part.optional [53, 48, 51, 49] record.lastBuyer,
   Part.optional [53, 48, 51, 50] record.lastSeller,
   Part.optional [53, 48, 53, 55] record.impliedPrice25,
   Part.optional [53, 48, 53, 51] record.userMsgCatReq,
   Part.optional [53, 48, 52, 56] record.sendMsgType,
   Part.optional [53, 48, 52, 57] record.sendMsgUserId,
   Part.optional [53, 48, 53, 48] record.sendMsgText,
   Part.optional [53, 48, 53, 49] record.quoteVolume,
   Part.optional [53, 48, 53, 50] record.quoteFirm]

def UserMessage.tags : List (List (List UInt8)) :=
  [[[53, 48, 48, 49]], [[49, 48, 48]], [[53, 53]], [[53, 48, 48, 52]], [[53, 48, 50, 49]], [[53, 56]], [[53, 48, 48, 51]], [[53, 48, 48, 50]], [[53, 48, 48, 57]], [[53, 48, 48, 53]], [[53, 48, 49, 48]], [[53, 48, 53, 52]], [[53, 48, 51, 54]], [[53, 48, 51, 51]], [[53, 48, 51, 52]], [[53, 48, 50, 56]], [[53, 48, 49, 51]], [[53, 48, 49, 52]], [[53, 48, 49, 55]], [[53, 48, 49, 56]], [[53, 48, 49, 57]], [[53, 48, 50, 48]], [[53, 48, 49, 54]], [[53, 48, 49, 53]], [[53, 48, 50, 50]], [[53, 48, 50, 51]], [[53, 48, 50, 52]], [[53, 48, 50, 53]], [[53, 48, 50, 54]], [[53, 48, 49, 49]], [[53, 48, 53, 53]], [[53, 48, 53, 54]], [[53, 48, 51, 49]], [[53, 48, 51, 50]], [[53, 48, 53, 55]], [[53, 48, 53, 51]], [[53, 48, 52, 56]], [[53, 48, 52, 57]], [[53, 48, 53, 48]], [[53, 48, 53, 49]], [[53, 48, 53, 50]]]

theorem UserMessage.shape (record : UserMessage) : record.parts.map Part.tags = UserMessage.tags := rfl

def UserMessage.decode (tokens : List Token) : Option UserMessage := do
  let userMsgCat ← readRequired [53, 48, 48, 49] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let currency ← readOptional [53, 48, 48, 52] tokens
  let fOBIndicator ← readOptional [53, 48, 50, 49] tokens
  let text ← readOptional [53, 56] tokens
  let lastMessage ← readOptional [53, 48, 48, 51] tokens
  let instrmntIndicator ← readOptional [53, 48, 48, 50] tokens
  let monthYear ← readOptional [53, 48, 48, 57] tokens
  let tickIncrement ← readOptional [53, 48, 48, 53] tokens
  let underlyingFut ← readOptional [53, 48, 49, 48] tokens
  let fractionalIndicator ← readOptional [53, 48, 53, 52] tokens
  let referenceNo ← readOptional [53, 48, 51, 54] tokens
  let filterType ← readOptional [53, 48, 51, 51] tokens
  let interSpreadsFlag ← readOptional [53, 48, 51, 52] tokens
  let interSprdRatio ← readOptional [53, 48, 50, 56] tokens
  let optionsStrikeP ← readOptional [53, 48, 49, 51] tokens
  let marketStatus ← readOptional [53, 48, 49, 52] tokens
  let settlementPrice ← readOptional [53, 48, 49, 55] tokens
  let volatility ← readOptional [53, 48, 49, 56] tokens
  let openPrice ← readOptional [53, 48, 49, 57] tokens
  let closePrice ← readOptional [53, 48, 50, 48] tokens
  let highTradePrice ← readOptional [53, 48, 49, 54] tokens
  let lowTradePrice ← readOptional [53, 48, 49, 53] tokens
  let askPrice ← readOptional [53, 48, 50, 50] tokens
  let askVolume ← readOptional [53, 48, 50, 51] tokens
  let bidPrice ← readOptional [53, 48, 50, 52] tokens
  let bidVolume ← readOptional [53, 48, 50, 53] tokens
  let lastTradedPrice ← readOptional [53, 48, 50, 54] tokens
  let lastTradedVolume ← readOptional [53, 48, 49, 49] tokens
  let totalTradedVolume ← readOptional [53, 48, 53, 53] tokens
  let interimSettlement ← readOptional [53, 48, 53, 54] tokens
  let lastBuyer ← readOptional [53, 48, 51, 49] tokens
  let lastSeller ← readOptional [53, 48, 51, 50] tokens
  let impliedPrice25 ← readOptional [53, 48, 53, 55] tokens
  let userMsgCatReq ← readOptional [53, 48, 53, 51] tokens
  let sendMsgType ← readOptional [53, 48, 52, 56] tokens
  let sendMsgUserId ← readOptional [53, 48, 52, 57] tokens
  let sendMsgText ← readOptional [53, 48, 53, 48] tokens
  let quoteVolume ← readOptional [53, 48, 53, 49] tokens
  let quoteFirm ← readOptional [53, 48, 53, 50] tokens
  pure { userMsgCat, exDestination, symbol, currency, fOBIndicator, text, lastMessage, instrmntIndicator, monthYear, tickIncrement, underlyingFut, fractionalIndicator, referenceNo, filterType, interSpreadsFlag, interSprdRatio, optionsStrikeP, marketStatus, settlementPrice, volatility, openPrice, closePrice, highTradePrice, lowTradePrice, askPrice, askVolume, bidPrice, bidVolume, lastTradedPrice, lastTradedVolume, totalTradedVolume, interimSettlement, lastBuyer, lastSeller, impliedPrice25, userMsgCatReq, sendMsgType, sendMsgUserId, sendMsgText, quoteVolume, quoteFirm }

theorem UserMessage.decode_agrees (record : UserMessage) (tokens : List Token)
    (agrees : ∀ tags ∈ UserMessage.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserMessage.decode tokens = some record := by
  have distinct : UserMessage.tags.flatten.Nodup := by decide +kernel
  have userMsgCat := readRequired_part [53, 48, 48, 49] record.userMsgCat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [53, 48, 48, 52] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have fOBIndicator := readOptional_part [53, 48, 50, 49] record.fOBIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastMessage := readOptional_part [53, 48, 48, 51] record.lastMessage tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have instrmntIndicator := readOptional_part [53, 48, 48, 50] record.instrmntIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have monthYear := readOptional_part [53, 48, 48, 57] record.monthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have tickIncrement := readOptional_part [53, 48, 48, 53] record.tickIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have underlyingFut := readOptional_part [53, 48, 49, 48] record.underlyingFut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have fractionalIndicator := readOptional_part [53, 48, 53, 52] record.fractionalIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have referenceNo := readOptional_part [53, 48, 51, 54] record.referenceNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have filterType := readOptional_part [53, 48, 51, 51] record.filterType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have interSpreadsFlag := readOptional_part [53, 48, 51, 52] record.interSpreadsFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have interSprdRatio := readOptional_part [53, 48, 50, 56] record.interSprdRatio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have optionsStrikeP := readOptional_part [53, 48, 49, 51] record.optionsStrikeP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have marketStatus := readOptional_part [53, 48, 49, 52] record.marketStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have settlementPrice := readOptional_part [53, 48, 49, 55] record.settlementPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have volatility := readOptional_part [53, 48, 49, 56] record.volatility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have openPrice := readOptional_part [53, 48, 49, 57] record.openPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have closePrice := readOptional_part [53, 48, 50, 48] record.closePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have highTradePrice := readOptional_part [53, 48, 49, 54] record.highTradePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lowTradePrice := readOptional_part [53, 48, 49, 53] record.lowTradePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have askPrice := readOptional_part [53, 48, 50, 50] record.askPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have askVolume := readOptional_part [53, 48, 50, 51] record.askVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have bidPrice := readOptional_part [53, 48, 50, 52] record.bidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have bidVolume := readOptional_part [53, 48, 50, 53] record.bidVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have lastTradedPrice := readOptional_part [53, 48, 50, 54] record.lastTradedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have lastTradedVolume := readOptional_part [53, 48, 49, 49] record.lastTradedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have totalTradedVolume := readOptional_part [53, 48, 53, 53] record.totalTradedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have interimSettlement := readOptional_part [53, 48, 53, 54] record.interimSettlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have lastBuyer := readOptional_part [53, 48, 51, 49] record.lastBuyer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have lastSeller := readOptional_part [53, 48, 51, 50] record.lastSeller tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have impliedPrice25 := readOptional_part [53, 48, 53, 55] record.impliedPrice25 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have userMsgCatReq := readOptional_part [53, 48, 53, 51] record.userMsgCatReq tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have sendMsgType := readOptional_part [53, 48, 52, 56] record.sendMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have sendMsgUserId := readOptional_part [53, 48, 52, 57] record.sendMsgUserId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have sendMsgText := readOptional_part [53, 48, 53, 48] record.sendMsgText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have quoteVolume := readOptional_part [53, 48, 53, 49] record.quoteVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have quoteFirm := readOptional_part [53, 48, 53, 50] record.quoteFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  simp only [UserMessage.decode, userMsgCat, exDestination, symbol, currency, fOBIndicator, text, lastMessage, instrmntIndicator, monthYear, tickIncrement, underlyingFut, fractionalIndicator, referenceNo, filterType, interSpreadsFlag, interSprdRatio, optionsStrikeP, marketStatus, settlementPrice, volatility, openPrice, closePrice, highTradePrice, lowTradePrice, askPrice, askVolume, bidPrice, bidVolume, lastTradedPrice, lastTradedVolume, totalTradedVolume, interimSettlement, lastBuyer, lastSeller, impliedPrice25, userMsgCatReq, sendMsgType, sendMsgUserId, sendMsgText, quoteVolume, quoteFirm, some_bind] <;> rfl

structure NoLegs where
  legPrice : Terminated 1  -- tag 5039
  legVolumeRatio : Option (Terminated 1)  -- tag 5040
  legSide : Option (Terminated 1)  -- tag 5041

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [53, 48, 51, 57] record.legPrice,
   Part.optional [53, 48, 52, 48] record.legVolumeRatio,
   Part.optional [53, 48, 52, 49] record.legSide]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[53, 48, 51, 57]], [[53, 48, 52, 48]], [[53, 48, 52, 49]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legPrice ← readRequired [53, 48, 51, 57] tokens
  let legVolumeRatio ← readOptional [53, 48, 52, 48] tokens
  let legSide ← readOptional [53, 48, 52, 49] tokens
  pure { legPrice, legVolumeRatio, legSide }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legPrice := readRequired_part [53, 48, 51, 57] record.legPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legVolumeRatio := readOptional_part [53, 48, 52, 48] record.legVolumeRatio tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSide := readOptional_part [53, 48, 52, 49] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoLegs.decode, legPrice, legVolumeRatio, legSide, some_bind] <;> rfl

def NoLegs.members : List (List UInt8) := NoLegs.tags.flatten

def NoLegs.encode (entry : NoLegs) : List Token := encodeParts entry.parts

theorem NoLegs.decode_encode (entry : NoLegs) : NoLegs.decode entry.encode = some entry :=
  NoLegs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLegs.within (entry : NoLegs) : ∀ token ∈ entry.encode, token.tag ∈ NoLegs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLegs.shape] at this

theorem NoLegs.led (entry : NoLegs) : Lead [53, 48, 51, 57] entry.encode :=
  lead_parts [53, 48, 51, 57] entry.legPrice _ NoLegs.tags.tail rfl (by decide +kernel)

structure NoAskLevels where
  askFirm : Terminated 1  -- tag 5043
  askVol : Option (Terminated 1)  -- tag 5044

def NoAskLevels.parts (record : NoAskLevels) : List Part :=
  [Part.required [53, 48, 52, 51] record.askFirm,
   Part.optional [53, 48, 52, 52] record.askVol]

def NoAskLevels.tags : List (List (List UInt8)) :=
  [[[53, 48, 52, 51]], [[53, 48, 52, 52]]]

theorem NoAskLevels.shape (record : NoAskLevels) : record.parts.map Part.tags = NoAskLevels.tags := rfl

def NoAskLevels.decode (tokens : List Token) : Option NoAskLevels := do
  let askFirm ← readRequired [53, 48, 52, 51] tokens
  let askVol ← readOptional [53, 48, 52, 52] tokens
  pure { askFirm, askVol }

theorem NoAskLevels.decode_agrees (record : NoAskLevels) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAskLevels.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAskLevels.decode tokens = some record := by
  have distinct : NoAskLevels.tags.flatten.Nodup := by decide +kernel
  have askFirm := readRequired_part [53, 48, 52, 51] record.askFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have askVol := readOptional_part [53, 48, 52, 52] record.askVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoAskLevels.decode, askFirm, askVol, some_bind] <;> rfl

def NoAskLevels.members : List (List UInt8) := NoAskLevels.tags.flatten

def NoAskLevels.encode (entry : NoAskLevels) : List Token := encodeParts entry.parts

theorem NoAskLevels.decode_encode (entry : NoAskLevels) : NoAskLevels.decode entry.encode = some entry :=
  NoAskLevels.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAskLevels.within (entry : NoAskLevels) : ∀ token ∈ entry.encode, token.tag ∈ NoAskLevels.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAskLevels.shape] at this

theorem NoAskLevels.led (entry : NoAskLevels) : Lead [53, 48, 52, 51] entry.encode :=
  lead_parts [53, 48, 52, 51] entry.askFirm _ NoAskLevels.tags.tail rfl (by decide +kernel)

structure NoBidLevels where
  bidFirm : Terminated 1  -- tag 5046
  bidVol : Option (Terminated 1)  -- tag 5047

def NoBidLevels.parts (record : NoBidLevels) : List Part :=
  [Part.required [53, 48, 52, 54] record.bidFirm,
   Part.optional [53, 48, 52, 55] record.bidVol]

def NoBidLevels.tags : List (List (List UInt8)) :=
  [[[53, 48, 52, 54]], [[53, 48, 52, 55]]]

theorem NoBidLevels.shape (record : NoBidLevels) : record.parts.map Part.tags = NoBidLevels.tags := rfl

def NoBidLevels.decode (tokens : List Token) : Option NoBidLevels := do
  let bidFirm ← readRequired [53, 48, 52, 54] tokens
  let bidVol ← readOptional [53, 48, 52, 55] tokens
  pure { bidFirm, bidVol }

theorem NoBidLevels.decode_agrees (record : NoBidLevels) (tokens : List Token)
    (agrees : ∀ tags ∈ NoBidLevels.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoBidLevels.decode tokens = some record := by
  have distinct : NoBidLevels.tags.flatten.Nodup := by decide +kernel
  have bidFirm := readRequired_part [53, 48, 52, 54] record.bidFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have bidVol := readOptional_part [53, 48, 52, 55] record.bidVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoBidLevels.decode, bidFirm, bidVol, some_bind] <;> rfl

def NoBidLevels.members : List (List UInt8) := NoBidLevels.tags.flatten

def NoBidLevels.encode (entry : NoBidLevels) : List Token := encodeParts entry.parts

theorem NoBidLevels.decode_encode (entry : NoBidLevels) : NoBidLevels.decode entry.encode = some entry :=
  NoBidLevels.decode_agrees entry _ (fun _ _ => rfl)

theorem NoBidLevels.within (entry : NoBidLevels) : ∀ token ∈ entry.encode, token.tag ∈ NoBidLevels.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoBidLevels.shape] at this

theorem NoBidLevels.led (entry : NoBidLevels) : Lead [53, 48, 52, 54] entry.encode :=
  lead_parts [53, 48, 52, 54] entry.bidFirm _ NoBidLevels.tags.tail rfl (by decide +kernel)

structure ExecutionReport where
  orderID : Terminated 1  -- tag 37
  execID : Terminated 1  -- tag 17
  clOrdID : Option (Terminated 1)  -- tag 11
  execTransType : Option (Terminated 1)  -- tag 20
  ordStatus : Terminated 1  -- tag 39
  ordRejReason : Option (Terminated 1)  -- tag 103
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  account : Option (Terminated 1)  -- tag 1
  orderQty : Option (Terminated 1)  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  lastShares : Option (Terminated 1)  -- tag 32
  cumQty : Option (Terminated 1)  -- tag 14
  transactTime : Option (Terminated 1)  -- tag 60
  execInst : Option (Terminated 1)  -- tag 18
  text : Option (Terminated 1)  -- tag 58
  sharedTradeIndicator : Option (Terminated 1)  -- tag 5059
  userMsgCat : Option (Terminated 1)  -- tag 5001
  referenceNo : Option (Terminated 1)  -- tag 5036
  filterType : Option (Terminated 1)  -- tag 5033
  exDestination : Option (Terminated 1)  -- tag 100
  interSpreadsFlag : Option (Terminated 1)  -- tag 5034
  enable : Option (Terminated 1)  -- tag 5035
  instrmntIndicator : Option (Terminated 1)  -- tag 5002
  monthYear : Option (Terminated 1)  -- tag 5009
  optionsStrikeP : Option (Terminated 1)  -- tag 5013
  changeStatusOf : Option (Terminated 1)  -- tag 5012
  marketStatus : Option (Terminated 1)  -- tag 5014
  lowTradePrice : Option (Terminated 1)  -- tag 5015
  highTradePrice : Option (Terminated 1)  -- tag 5016
  settlementPrice : Option (Terminated 1)  -- tag 5017
  openPrice : Option (Terminated 1)  -- tag 5019
  closePrice : Option (Terminated 1)  -- tag 5020
  askPrice : Option (Terminated 1)  -- tag 5022
  askVolume : Option (Terminated 1)  -- tag 5023
  bidPrice : Option (Terminated 1)  -- tag 5024
  bidVolume : Option (Terminated 1)  -- tag 5025
  impliedPrice25 : Option (Terminated 1)  -- tag 5057
  lastTradedPrice : Option (Terminated 1)  -- tag 5026
  lastTradedVolume : Option (Terminated 1)  -- tag 5011
  lastBuyer : Option (Terminated 1)  -- tag 5031
  lastSeller : Option (Terminated 1)  -- tag 5032
  totalTradedVolume : Option (Terminated 1)  -- tag 5055
  volatility : Option (Terminated 1)  -- tag 5018
  interimSettlement : Option (Terminated 1)  -- tag 5056
  customVolume : Option (Terminated 1)  -- tag 5037
  noLegs : List NoLegs  -- tag 5038
  noAskLevels : List NoAskLevels  -- tag 5042
  noBidLevels : List NoBidLevels  -- tag 5045

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.required [51, 55] record.orderID,
   Part.required [49, 55] record.execID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [50, 48] record.execTransType,
   Part.required [51, 57] record.ordStatus,
   Part.optional [49, 48, 51] record.ordRejReason,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [49] record.account,
   Part.optional [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [51, 50] record.lastShares,
   Part.optional [49, 52] record.cumQty,
   Part.optional [54, 48] record.transactTime,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 56] record.text,
   Part.optional [53, 48, 53, 57] record.sharedTradeIndicator,
   Part.optional [53, 48, 48, 49] record.userMsgCat,
   Part.optional [53, 48, 51, 54] record.referenceNo,
   Part.optional [53, 48, 51, 51] record.filterType,
   Part.optional [49, 48, 48] record.exDestination,
   Part.optional [53, 48, 51, 52] record.interSpreadsFlag,
   Part.optional [53, 48, 51, 53] record.enable,
   Part.optional [53, 48, 48, 50] record.instrmntIndicator,
   Part.optional [53, 48, 48, 57] record.monthYear,
   Part.optional [53, 48, 49, 51] record.optionsStrikeP,
   Part.optional [53, 48, 49, 50] record.changeStatusOf,
   Part.optional [53, 48, 49, 52] record.marketStatus,
   Part.optional [53, 48, 49, 53] record.lowTradePrice,
   Part.optional [53, 48, 49, 54] record.highTradePrice,
   Part.optional [53, 48, 49, 55] record.settlementPrice,
   Part.optional [53, 48, 49, 57] record.openPrice,
   Part.optional [53, 48, 50, 48] record.closePrice,
   Part.optional [53, 48, 50, 50] record.askPrice,
   Part.optional [53, 48, 50, 51] record.askVolume,
   Part.optional [53, 48, 50, 52] record.bidPrice,
   Part.optional [53, 48, 50, 53] record.bidVolume,
   Part.optional [53, 48, 53, 55] record.impliedPrice25,
   Part.optional [53, 48, 50, 54] record.lastTradedPrice,
   Part.optional [53, 48, 49, 49] record.lastTradedVolume,
   Part.optional [53, 48, 51, 49] record.lastBuyer,
   Part.optional [53, 48, 51, 50] record.lastSeller,
   Part.optional [53, 48, 53, 53] record.totalTradedVolume,
   Part.optional [53, 48, 49, 56] record.volatility,
   Part.optional [53, 48, 53, 54] record.interimSettlement,
   Part.optional [53, 48, 51, 55] record.customVolume,
   Part.group [53, 48, 51, 56] NoLegs.members NoLegs.encode NoLegs.within record.noLegs,
   Part.group [53, 48, 52, 50] NoAskLevels.members NoAskLevels.encode NoAskLevels.within record.noAskLevels,
   Part.group [53, 48, 52, 53] NoBidLevels.members NoBidLevels.encode NoBidLevels.within record.noBidLevels]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 55]], [[49, 49]], [[50, 48]], [[51, 57]], [[49, 48, 51]], [[53, 52]], [[53, 53]], [[49]], [[51, 56]], [[52, 48]], [[52, 52]], [[51, 50]], [[49, 52]], [[54, 48]], [[49, 56]], [[53, 56]], [[53, 48, 53, 57]], [[53, 48, 48, 49]], [[53, 48, 51, 54]], [[53, 48, 51, 51]], [[49, 48, 48]], [[53, 48, 51, 52]], [[53, 48, 51, 53]], [[53, 48, 48, 50]], [[53, 48, 48, 57]], [[53, 48, 49, 51]], [[53, 48, 49, 50]], [[53, 48, 49, 52]], [[53, 48, 49, 53]], [[53, 48, 49, 54]], [[53, 48, 49, 55]], [[53, 48, 49, 57]], [[53, 48, 50, 48]], [[53, 48, 50, 50]], [[53, 48, 50, 51]], [[53, 48, 50, 52]], [[53, 48, 50, 53]], [[53, 48, 53, 55]], [[53, 48, 50, 54]], [[53, 48, 49, 49]], [[53, 48, 51, 49]], [[53, 48, 51, 50]], [[53, 48, 53, 53]], [[53, 48, 49, 56]], [[53, 48, 53, 54]], [[53, 48, 51, 55]], [53, 48, 51, 56] :: NoLegs.members, [53, 48, 52, 50] :: NoAskLevels.members, [53, 48, 52, 53] :: NoBidLevels.members]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let orderID ← readRequired [51, 55] tokens
  let execID ← readRequired [49, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let execTransType ← readOptional [50, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordRejReason ← readOptional [49, 48, 51] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let account ← readOptional [49] tokens
  let orderQty ← readOptional [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let lastShares ← readOptional [51, 50] tokens
  let cumQty ← readOptional [49, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let execInst ← readOptional [49, 56] tokens
  let text ← readOptional [53, 56] tokens
  let sharedTradeIndicator ← readOptional [53, 48, 53, 57] tokens
  let userMsgCat ← readOptional [53, 48, 48, 49] tokens
  let referenceNo ← readOptional [53, 48, 51, 54] tokens
  let filterType ← readOptional [53, 48, 51, 51] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let interSpreadsFlag ← readOptional [53, 48, 51, 52] tokens
  let enable ← readOptional [53, 48, 51, 53] tokens
  let instrmntIndicator ← readOptional [53, 48, 48, 50] tokens
  let monthYear ← readOptional [53, 48, 48, 57] tokens
  let optionsStrikeP ← readOptional [53, 48, 49, 51] tokens
  let changeStatusOf ← readOptional [53, 48, 49, 50] tokens
  let marketStatus ← readOptional [53, 48, 49, 52] tokens
  let lowTradePrice ← readOptional [53, 48, 49, 53] tokens
  let highTradePrice ← readOptional [53, 48, 49, 54] tokens
  let settlementPrice ← readOptional [53, 48, 49, 55] tokens
  let openPrice ← readOptional [53, 48, 49, 57] tokens
  let closePrice ← readOptional [53, 48, 50, 48] tokens
  let askPrice ← readOptional [53, 48, 50, 50] tokens
  let askVolume ← readOptional [53, 48, 50, 51] tokens
  let bidPrice ← readOptional [53, 48, 50, 52] tokens
  let bidVolume ← readOptional [53, 48, 50, 53] tokens
  let impliedPrice25 ← readOptional [53, 48, 53, 55] tokens
  let lastTradedPrice ← readOptional [53, 48, 50, 54] tokens
  let lastTradedVolume ← readOptional [53, 48, 49, 49] tokens
  let lastBuyer ← readOptional [53, 48, 51, 49] tokens
  let lastSeller ← readOptional [53, 48, 51, 50] tokens
  let totalTradedVolume ← readOptional [53, 48, 53, 53] tokens
  let volatility ← readOptional [53, 48, 49, 56] tokens
  let interimSettlement ← readOptional [53, 48, 53, 54] tokens
  let customVolume ← readOptional [53, 48, 51, 55] tokens
  let noLegs ← readGroup [53, 48, 51, 56] [53, 48, 51, 57] NoLegs.members NoLegs.decode tokens
  let noAskLevels ← readGroup [53, 48, 52, 50] [53, 48, 52, 51] NoAskLevels.members NoAskLevels.decode tokens
  let noBidLevels ← readGroup [53, 48, 52, 53] [53, 48, 52, 54] NoBidLevels.members NoBidLevels.decode tokens
  pure { orderID, execID, clOrdID, execTransType, ordStatus, ordRejReason, side, symbol, account, orderQty, ordType, price, lastShares, cumQty, transactTime, execInst, text, sharedTradeIndicator, userMsgCat, referenceNo, filterType, exDestination, interSpreadsFlag, enable, instrmntIndicator, monthYear, optionsStrikeP, changeStatusOf, marketStatus, lowTradePrice, highTradePrice, settlementPrice, openPrice, closePrice, askPrice, askVolume, bidPrice, bidVolume, impliedPrice25, lastTradedPrice, lastTradedVolume, lastBuyer, lastSeller, totalTradedVolume, volatility, interimSettlement, customVolume, noLegs, noAskLevels, noBidLevels }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordRejReason := readOptional_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have lastShares := readOptional_part [51, 50] record.lastShares tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have sharedTradeIndicator := readOptional_part [53, 48, 53, 57] record.sharedTradeIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have userMsgCat := readOptional_part [53, 48, 48, 49] record.userMsgCat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have referenceNo := readOptional_part [53, 48, 51, 54] record.referenceNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have filterType := readOptional_part [53, 48, 51, 51] record.filterType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have interSpreadsFlag := readOptional_part [53, 48, 51, 52] record.interSpreadsFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have enable := readOptional_part [53, 48, 51, 53] record.enable tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have instrmntIndicator := readOptional_part [53, 48, 48, 50] record.instrmntIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have monthYear := readOptional_part [53, 48, 48, 57] record.monthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have optionsStrikeP := readOptional_part [53, 48, 49, 51] record.optionsStrikeP tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have changeStatusOf := readOptional_part [53, 48, 49, 50] record.changeStatusOf tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have marketStatus := readOptional_part [53, 48, 49, 52] record.marketStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have lowTradePrice := readOptional_part [53, 48, 49, 53] record.lowTradePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have highTradePrice := readOptional_part [53, 48, 49, 54] record.highTradePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have settlementPrice := readOptional_part [53, 48, 49, 55] record.settlementPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have openPrice := readOptional_part [53, 48, 49, 57] record.openPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have closePrice := readOptional_part [53, 48, 50, 48] record.closePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have askPrice := readOptional_part [53, 48, 50, 50] record.askPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have askVolume := readOptional_part [53, 48, 50, 51] record.askVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have bidPrice := readOptional_part [53, 48, 50, 52] record.bidPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have bidVolume := readOptional_part [53, 48, 50, 53] record.bidVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have impliedPrice25 := readOptional_part [53, 48, 53, 55] record.impliedPrice25 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have lastTradedPrice := readOptional_part [53, 48, 50, 54] record.lastTradedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have lastTradedVolume := readOptional_part [53, 48, 49, 49] record.lastTradedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have lastBuyer := readOptional_part [53, 48, 51, 49] record.lastBuyer tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have lastSeller := readOptional_part [53, 48, 51, 50] record.lastSeller tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have totalTradedVolume := readOptional_part [53, 48, 53, 53] record.totalTradedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have volatility := readOptional_part [53, 48, 49, 56] record.volatility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have interimSettlement := readOptional_part [53, 48, 53, 54] record.interimSettlement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have customVolume := readOptional_part [53, 48, 51, 55] record.customVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have noLegs := readGroup_part [53, 48, 51, 56] [53, 48, 51, 57] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have noAskLevels := readGroup_part [53, 48, 52, 50] [53, 48, 52, 51] NoAskLevels.members NoAskLevels.encode NoAskLevels.within NoAskLevels.decode NoAskLevels.decode_encode NoAskLevels.led record.noAskLevels tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have noBidLevels := readGroup_part [53, 48, 52, 53] [53, 48, 52, 54] NoBidLevels.members NoBidLevels.encode NoBidLevels.within NoBidLevels.decode NoBidLevels.decode_encode NoBidLevels.led record.noBidLevels tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  simp only [ExecutionReport.decode, orderID, execID, clOrdID, execTransType, ordStatus, ordRejReason, side, symbol, account, orderQty, ordType, price, lastShares, cumQty, transactTime, execInst, text, sharedTradeIndicator, userMsgCat, referenceNo, filterType, exDestination, interSpreadsFlag, enable, instrmntIndicator, monthYear, optionsStrikeP, changeStatusOf, marketStatus, lowTradePrice, highTradePrice, settlementPrice, openPrice, closePrice, askPrice, askVolume, bidPrice, bidVolume, impliedPrice25, lastTradedPrice, lastTradedVolume, lastBuyer, lastSeller, totalTradedVolume, volatility, interimSettlement, customVolume, noLegs, noAskLevels, noBidLevels, some_bind] <;> rfl

structure OrderCancelReject where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58
  userMsgCat : Option (Terminated 1)  -- tag 5001
  referenceNo : Option (Terminated 1)  -- tag 5036
  execID : Option (Terminated 1)  -- tag 17
  side : Option (Terminated 1)  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  account : Option (Terminated 1)  -- tag 1

def OrderCancelReject.parts (record : OrderCancelReject) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [53, 48, 48, 49] record.userMsgCat,
   Part.optional [53, 48, 51, 54] record.referenceNo,
   Part.optional [49, 55] record.execID,
   Part.optional [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [49] record.account]

def OrderCancelReject.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[49, 48, 50]], [[53, 56]], [[53, 48, 48, 49]], [[53, 48, 51, 54]], [[49, 55]], [[53, 52]], [[53, 53]], [[49]]]

theorem OrderCancelReject.shape (record : OrderCancelReject) : record.parts.map Part.tags = OrderCancelReject.tags := rfl

def OrderCancelReject.decode (tokens : List Token) : Option OrderCancelReject := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  let userMsgCat ← readOptional [53, 48, 48, 49] tokens
  let referenceNo ← readOptional [53, 48, 51, 54] tokens
  let execID ← readOptional [49, 55] tokens
  let side ← readOptional [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let account ← readOptional [49] tokens
  pure { orderID, clOrdID, cxlRejReason, text, userMsgCat, referenceNo, execID, side, symbol, account }

theorem OrderCancelReject.decode_agrees (record : OrderCancelReject) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReject.decode tokens = some record := by
  have distinct : OrderCancelReject.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have userMsgCat := readOptional_part [53, 48, 48, 49] record.userMsgCat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have referenceNo := readOptional_part [53, 48, 51, 54] record.referenceNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execID := readOptional_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderCancelReject.decode, orderID, clOrdID, cxlRejReason, text, userMsgCat, referenceNo, execID, side, symbol, account, some_bind] <;> rfl

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | testRequest (header : Header) (r0 : TestRequest)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | reject (header : Header) (r0 : Reject)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | logout (header : Header) (r0 : Logout)
  | userMessage (header : Header) (r0 : UserMessage)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | orderCancelReject (header : Header) (r0 : OrderCancelReject)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], ⟨[65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], ⟨[48], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], ⟨[49], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], ⟨[50], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], ⟨[51], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], ⟨[52], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], ⟨[53], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userMessage header r0 => ⟨[51, 53], ⟨[85], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value.val = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value.val = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value.val = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value.val = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value.val = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value.val = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value.val = [85] then
        if known (Header.tags ++ UserMessage.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserMessage.decode rest
          pure (.userMessage header r0)
        else none
      else if token.value.val = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ OrderCancelReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReject.decode rest
          pure (.orderCancelReject header r0)
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

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userMessage (header : Header) (r0 : UserMessage) :
    Message.decode (Message.tokens (.userMessage header r0)) = some (.userMessage header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserMessage.tags) rfl rfl (by decide +kernel))
  have c1 := UserMessage.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserMessage.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserMessage.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decode (Message.tokens (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | logout header r0 => exact Message.decode_logout header r0
  | userMessage header r0 => exact Message.decode_userMessage header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | orderCancelReject header r0 => exact Message.decode_orderCancelReject header r0

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

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[48], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[49], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[50], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[51], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Reject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[52], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[53], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Logout.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_userMessage (header : Header) (r0 : UserMessage) :
    Message.decodeBytes (Message.encode (.userMessage header r0)) = some (.userMessage header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[85], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ UserMessage.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userMessage header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

theorem Message.decodeBytes_orderCancelReject (header : Header) (r0 : OrderCancelReject) :
    Message.decodeBytes (Message.encode (.orderCancelReject header r0)) = some (.orderCancelReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | userMessage header r0 => exact Message.decodeBytes_userMessage header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | orderCancelReject header r0 => exact Message.decodeBytes_orderCancelReject header r0

/-- BeginString as the venue fixes it: FIX.4.0 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 48, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AsxAsxderivativesTrade24FixV10Exchange
