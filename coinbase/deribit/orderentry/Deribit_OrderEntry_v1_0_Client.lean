import Wire

/-!
# Coinbase Order Entry v1.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CoinbaseDeribitOrderentryFixV10Client

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 53], [57, 54])]

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Option (Terminated 1)  -- tag 52

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [53, 50] record.sendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[51, 52]], [[53, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readOptional [53, 50] tokens
  pure { senderCompID, targetCompID, msgSeqNum, sendingTime }

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
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, msgSeqNum, sendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_none pairing))))

structure Heartbeat where
  testReqId : Option (Terminated 1)  -- tag 112

def Heartbeat.parts (record : Heartbeat) : List Part :=
  [Part.optional [49, 49, 50] record.testReqId]

def Heartbeat.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (tokens : List Token) : Option Heartbeat := do
  let testReqId ← readOptional [49, 49, 50] tokens
  pure { testReqId }

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (agrees : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  have distinct : Heartbeat.tags.flatten.Nodup := by decide +kernel
  have testReqId := readOptional_part [49, 49, 50] record.testReqId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Heartbeat.decode, testReqId, some_bind] <;> rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqId (by decide) (by decide))
   (paired_none pairing)

structure Logon where
  heartBtInt : Terminated 1  -- tag 108
  rawData : List UInt8  -- tag 96
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554
  useWordsafeTags : Option (Terminated 1)  -- tag 9002
  cancelOnDisconnect : Option (Terminated 1)  -- tag 9001
  deribitAppId : Option (Terminated 1)  -- tag 9004
  deribitAppSig : Option (Terminated 1)  -- tag 9005
  deribitSequential : Option (Terminated 1)  -- tag 9007
  unsubscribeExecutionReports : Option (Terminated 1)  -- tag 9009
  connectionOnlyExecutionReports : Option (Terminated 1)  -- tag 9010
  reportFillsAsExecReports : Option (Terminated 1)  -- tag 9015
  displayIncrementSteps : Option (Terminated 1)  -- tag 9018

def Logon.parts (record : Logon) : List Part :=
  [Part.required [49, 48, 56] record.heartBtInt,
   Part.dataRequired [57, 53] [57, 54] record.rawData,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password,
   Part.optional [57, 48, 48, 50] record.useWordsafeTags,
   Part.optional [57, 48, 48, 49] record.cancelOnDisconnect,
   Part.optional [57, 48, 48, 52] record.deribitAppId,
   Part.optional [57, 48, 48, 53] record.deribitAppSig,
   Part.optional [57, 48, 48, 55] record.deribitSequential,
   Part.optional [57, 48, 48, 57] record.unsubscribeExecutionReports,
   Part.optional [57, 48, 49, 48] record.connectionOnlyExecutionReports,
   Part.optional [57, 48, 49, 53] record.reportFillsAsExecReports,
   Part.optional [57, 48, 49, 56] record.displayIncrementSteps]

def Logon.tags : List (List (List UInt8)) :=
  [[[49, 48, 56]], [[57, 53], [57, 54]], [[53, 53, 51]], [[53, 53, 52]], [[57, 48, 48, 50]], [[57, 48, 48, 49]], [[57, 48, 48, 52]], [[57, 48, 48, 53]], [[57, 48, 48, 55]], [[57, 48, 48, 57]], [[57, 48, 49, 48]], [[57, 48, 49, 53]], [[57, 48, 49, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawData ← readData [57, 53] [57, 54] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  let useWordsafeTags ← readOptional [57, 48, 48, 50] tokens
  let cancelOnDisconnect ← readOptional [57, 48, 48, 49] tokens
  let deribitAppId ← readOptional [57, 48, 48, 52] tokens
  let deribitAppSig ← readOptional [57, 48, 48, 53] tokens
  let deribitSequential ← readOptional [57, 48, 48, 55] tokens
  let unsubscribeExecutionReports ← readOptional [57, 48, 48, 57] tokens
  let connectionOnlyExecutionReports ← readOptional [57, 48, 49, 48] tokens
  let reportFillsAsExecReports ← readOptional [57, 48, 49, 53] tokens
  let displayIncrementSteps ← readOptional [57, 48, 49, 56] tokens
  pure { heartBtInt, rawData, username, password, useWordsafeTags, cancelOnDisconnect, deribitAppId, deribitAppSig, deribitSequential, unsubscribeExecutionReports, connectionOnlyExecutionReports, reportFillsAsExecReports, displayIncrementSteps }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rawData := readData_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have useWordsafeTags := readOptional_part [57, 48, 48, 50] record.useWordsafeTags tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cancelOnDisconnect := readOptional_part [57, 48, 48, 49] record.cancelOnDisconnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deribitAppId := readOptional_part [57, 48, 48, 52] record.deribitAppId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deribitAppSig := readOptional_part [57, 48, 48, 53] record.deribitAppSig tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have deribitSequential := readOptional_part [57, 48, 48, 55] record.deribitSequential tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have unsubscribeExecutionReports := readOptional_part [57, 48, 48, 57] record.unsubscribeExecutionReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have connectionOnlyExecutionReports := readOptional_part [57, 48, 49, 48] record.connectionOnlyExecutionReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have reportFillsAsExecReports := readOptional_part [57, 48, 49, 53] record.reportFillsAsExecReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displayIncrementSteps := readOptional_part [57, 48, 49, 56] record.displayIncrementSteps tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [Logon.decode, heartBtInt, rawData, username, password, useWordsafeTags, cancelOnDisconnect, deribitAppId, deribitAppSig, deribitSequential, unsubscribeExecutionReports, connectionOnlyExecutionReports, reportFillsAsExecReports, displayIncrementSteps, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
   (paired_cons pairing _ _ (paired_dataRequired pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53, 52] record.password (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 50] record.useWordsafeTags (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 49] record.cancelOnDisconnect (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 52] record.deribitAppId (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 53] record.deribitAppSig (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 55] record.deribitSequential (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 57] record.unsubscribeExecutionReports (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 48] record.connectionOnlyExecutionReports (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 53] record.reportFillsAsExecReports (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 56] record.displayIncrementSteps (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure Logout where
  text : Option (Terminated 1)  -- tag 58
  dontCancelOnDisconnect : Option (Terminated 1)  -- tag 9003

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.optional [57, 48, 48, 51] record.dontCancelOnDisconnect]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[57, 48, 48, 51]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  let dontCancelOnDisconnect ← readOptional [57, 48, 48, 51] tokens
  pure { text, dontCancelOnDisconnect }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have dontCancelOnDisconnect := readOptional_part [57, 48, 48, 51] record.dontCancelOnDisconnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, text, dontCancelOnDisconnect, some_bind] <;> rfl

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 51] record.dontCancelOnDisconnect (by decide) (by decide))
    (paired_none pairing))

structure NoMdEntryTypes where
  mDEntryType : Terminated 1  -- tag 269

def NoMdEntryTypes.parts (record : NoMdEntryTypes) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType]

def NoMdEntryTypes.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]]]

theorem NoMdEntryTypes.shape (record : NoMdEntryTypes) : record.parts.map Part.tags = NoMdEntryTypes.tags := rfl

def NoMdEntryTypes.decode (tokens : List Token) : Option NoMdEntryTypes := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  pure { mDEntryType }

theorem NoMdEntryTypes.decode_agrees (record : NoMdEntryTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMdEntryTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMdEntryTypes.decode tokens = some record := by
  have distinct : NoMdEntryTypes.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoMdEntryTypes.decode, mDEntryType, some_bind] <;> rfl

theorem NoMdEntryTypes.taken (record : NoMdEntryTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
   (paired_none pairing)

def NoMdEntryTypes.members : List (List UInt8) := NoMdEntryTypes.tags.flatten

def NoMdEntryTypes.encode (entry : NoMdEntryTypes) : List Token := encodeParts entry.parts

theorem NoMdEntryTypes.decode_encode (entry : NoMdEntryTypes) : NoMdEntryTypes.decode entry.encode = some entry :=
  NoMdEntryTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMdEntryTypes.within (entry : NoMdEntryTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoMdEntryTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMdEntryTypes.shape] at this

theorem NoMdEntryTypes.led (entry : NoMdEntryTypes) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMdEntryTypes.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityDesc : Option (Terminated 1)  -- tag 107
  securityType : Option (Terminated 1)  -- tag 167
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  strikeCurrency : Option (Terminated 1)  -- tag 947
  currency : Option (Terminated 1)  -- tag 15
  priceQuoteCurrency : Option (Terminated 1)  -- tag 1524
  instrumentPricePrecision : Option (Terminated 1)  -- tag 2576
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  underlyingSymbol : Option (Terminated 1)  -- tag 311
  issueDate : Option (Terminated 1)  -- tag 225
  maturityDate : Option (Terminated 1)  -- tag 541
  maturityTime : Option (Terminated 1)  -- tag 1079
  minTradeVol : Option (Terminated 1)  -- tag 562
  settlType : Option (Terminated 1)  -- tag 63
  settlCurrency : Option (Terminated 1)  -- tag 120
  commCurrency : Option (Terminated 1)  -- tag 479
  contractMultiplier : Option (Terminated 1)  -- tag 231
  noSecurityAltID : Option (Terminated 1)  -- tag 454
  securityAltID : Option (Terminated 1)  -- tag 455
  securityAltIDSource : Option (Terminated 1)  -- tag 456
  noTickRules : Option (Terminated 1)  -- tag 1205
  startTickPriceRange : Option (Terminated 1)  -- tag 1206
  tickIncrement : Option (Terminated 1)  -- tag 1208
  securityStatus : Option (Terminated 1)  -- tag 965

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [57, 52, 55] record.strikeCurrency,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 53, 50, 52] record.priceQuoteCurrency,
   Part.optional [50, 53, 55, 54] record.instrumentPricePrecision,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.optional [51, 49, 49] record.underlyingSymbol,
   Part.optional [50, 50, 53] record.issueDate,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [49, 48, 55, 57] record.maturityTime,
   Part.optional [53, 54, 50] record.minTradeVol,
   Part.optional [54, 51] record.settlType,
   Part.optional [49, 50, 48] record.settlCurrency,
   Part.optional [52, 55, 57] record.commCurrency,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [52, 53, 52] record.noSecurityAltID,
   Part.optional [52, 53, 53] record.securityAltID,
   Part.optional [52, 53, 54] record.securityAltIDSource,
   Part.optional [49, 50, 48, 53] record.noTickRules,
   Part.optional [49, 50, 48, 54] record.startTickPriceRange,
   Part.optional [49, 50, 48, 56] record.tickIncrement,
   Part.optional [57, 54, 53] record.securityStatus]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[49, 48, 55]], [[49, 54, 55]], [[50, 48, 49]], [[50, 48, 50]], [[57, 52, 55]], [[49, 53]], [[49, 53, 50, 52]], [[50, 53, 55, 54]], [[57, 54, 57]], [[51, 49, 49]], [[50, 50, 53]], [[53, 52, 49]], [[49, 48, 55, 57]], [[53, 54, 50]], [[54, 51]], [[49, 50, 48]], [[52, 55, 57]], [[50, 51, 49]], [[52, 53, 52]], [[52, 53, 53]], [[52, 53, 54]], [[49, 50, 48, 53]], [[49, 50, 48, 54]], [[49, 50, 48, 56]], [[57, 54, 53]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let strikeCurrency ← readOptional [57, 52, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let priceQuoteCurrency ← readOptional [49, 53, 50, 52] tokens
  let instrumentPricePrecision ← readOptional [50, 53, 55, 54] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let underlyingSymbol ← readOptional [51, 49, 49] tokens
  let issueDate ← readOptional [50, 50, 53] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let maturityTime ← readOptional [49, 48, 55, 57] tokens
  let minTradeVol ← readOptional [53, 54, 50] tokens
  let settlType ← readOptional [54, 51] tokens
  let settlCurrency ← readOptional [49, 50, 48] tokens
  let commCurrency ← readOptional [52, 55, 57] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let noSecurityAltID ← readOptional [52, 53, 52] tokens
  let securityAltID ← readOptional [52, 53, 53] tokens
  let securityAltIDSource ← readOptional [52, 53, 54] tokens
  let noTickRules ← readOptional [49, 50, 48, 53] tokens
  let startTickPriceRange ← readOptional [49, 50, 48, 54] tokens
  let tickIncrement ← readOptional [49, 50, 48, 56] tokens
  let securityStatus ← readOptional [57, 54, 53] tokens
  pure { symbol, securityDesc, securityType, putOrCall, strikePrice, strikeCurrency, currency, priceQuoteCurrency, instrumentPricePrecision, minPriceIncrement, underlyingSymbol, issueDate, maturityDate, maturityTime, minTradeVol, settlType, settlCurrency, commCurrency, contractMultiplier, noSecurityAltID, securityAltID, securityAltIDSource, noTickRules, startTickPriceRange, tickIncrement, securityStatus }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have strikeCurrency := readOptional_part [57, 52, 55] record.strikeCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have priceQuoteCurrency := readOptional_part [49, 53, 50, 52] record.priceQuoteCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have instrumentPricePrecision := readOptional_part [50, 53, 55, 54] record.instrumentPricePrecision tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have underlyingSymbol := readOptional_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have issueDate := readOptional_part [50, 50, 53] record.issueDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have maturityTime := readOptional_part [49, 48, 55, 57] record.maturityTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minTradeVol := readOptional_part [53, 54, 50] record.minTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have settlCurrency := readOptional_part [49, 50, 48] record.settlCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have commCurrency := readOptional_part [52, 55, 57] record.commCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noSecurityAltID := readOptional_part [52, 53, 52] record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityAltID := readOptional_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have securityAltIDSource := readOptional_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noTickRules := readOptional_part [49, 50, 48, 53] record.noTickRules tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have startTickPriceRange := readOptional_part [49, 50, 48, 54] record.startTickPriceRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have tickIncrement := readOptional_part [49, 50, 48, 56] record.tickIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have securityStatus := readOptional_part [57, 54, 53] record.securityStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityDesc, securityType, putOrCall, strikePrice, strikeCurrency, currency, priceQuoteCurrency, instrumentPricePrecision, minPriceIncrement, underlyingSymbol, issueDate, maturityDate, maturityTime, minTradeVol, settlType, settlCurrency, commCurrency, contractMultiplier, noSecurityAltID, securityAltID, securityAltIDSource, noTickRules, startTickPriceRange, tickIncrement, securityStatus, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 52, 55] record.strikeCurrency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50, 52] record.priceQuoteCurrency (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 53, 55, 54] record.instrumentPricePrecision (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 50, 53] record.issueDate (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55, 57] record.maturityTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 54, 50] record.minTradeVol (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48] record.settlCurrency (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [52, 55, 57] record.commCurrency (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 53, 52] record.noSecurityAltID (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [52, 53, 53] record.securityAltID (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 53, 54] record.securityAltIDSource (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 53] record.noTickRules (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 54] record.startTickPriceRange (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48, 56] record.tickIncrement (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 54, 53] record.securityStatus (by decide) (by decide))
                            (paired_none pairing))))))))))))))))))))))))))

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure MarketDataRequest where
  mDReqID : Terminated 1  -- tag 262
  subscriptionRequestType : Terminated 1  -- tag 263
  marketDepth : Option (Terminated 1)  -- tag 264
  mDUpdateType : Option (Terminated 1)  -- tag 265
  deribitSkipBlockTrades : Option (Terminated 1)  -- tag 9011
  deribitShowBlockTradeId : Option (Terminated 1)  -- tag 9012
  deribitTradeAmount : Option (Terminated 1)  -- tag 100007
  deribitSinceTimestamp : Option (Terminated 1)  -- tag 100008
  noMdEntryTypes : List NoMdEntryTypes  -- tag 267
  noRelatedSym : List NoRelatedSym  -- tag 146

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.optional [50, 54, 52] record.marketDepth,
   Part.optional [50, 54, 53] record.mDUpdateType,
   Part.optional [57, 48, 49, 49] record.deribitSkipBlockTrades,
   Part.optional [57, 48, 49, 50] record.deribitShowBlockTradeId,
   Part.optional [49, 48, 48, 48, 48, 55] record.deribitTradeAmount,
   Part.optional [49, 48, 48, 48, 48, 56] record.deribitSinceTimestamp,
   Part.group [50, 54, 55] NoMdEntryTypes.members NoMdEntryTypes.encode NoMdEntryTypes.within record.noMdEntryTypes,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [[50, 54, 52]], [[50, 54, 53]], [[57, 48, 49, 49]], [[57, 48, 49, 50]], [[49, 48, 48, 48, 48, 55]], [[49, 48, 48, 48, 48, 56]], [50, 54, 55] :: NoMdEntryTypes.members, [49, 52, 54] :: NoRelatedSym.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let marketDepth ← readOptional [50, 54, 52] tokens
  let mDUpdateType ← readOptional [50, 54, 53] tokens
  let deribitSkipBlockTrades ← readOptional [57, 48, 49, 49] tokens
  let deribitShowBlockTradeId ← readOptional [57, 48, 49, 50] tokens
  let deribitTradeAmount ← readOptional [49, 48, 48, 48, 48, 55] tokens
  let deribitSinceTimestamp ← readOptional [49, 48, 48, 48, 48, 56] tokens
  let noMdEntryTypes ← readGroup [50, 54, 55] [50, 54, 57] NoMdEntryTypes.members NoMdEntryTypes.decode tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, deribitSkipBlockTrades, deribitShowBlockTradeId, deribitTradeAmount, deribitSinceTimestamp, noMdEntryTypes, noRelatedSym }

theorem MarketDataRequest.decode_agrees (record : MarketDataRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequest.decode tokens = some record := by
  have distinct : MarketDataRequest.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketDepth := readOptional_part [50, 54, 52] record.marketDepth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDUpdateType := readOptional_part [50, 54, 53] record.mDUpdateType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have deribitSkipBlockTrades := readOptional_part [57, 48, 49, 49] record.deribitSkipBlockTrades tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deribitShowBlockTradeId := readOptional_part [57, 48, 49, 50] record.deribitShowBlockTradeId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deribitTradeAmount := readOptional_part [49, 48, 48, 48, 48, 55] record.deribitTradeAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deribitSinceTimestamp := readOptional_part [49, 48, 48, 48, 48, 56] record.deribitSinceTimestamp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noMdEntryTypes := readGroup_part [50, 54, 55] [50, 54, 57] NoMdEntryTypes.members NoMdEntryTypes.encode NoMdEntryTypes.within NoMdEntryTypes.decode NoMdEntryTypes.decode_encode NoMdEntryTypes.led record.noMdEntryTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, marketDepth, mDUpdateType, deribitSkipBlockTrades, deribitShowBlockTradeId, deribitTradeAmount, deribitSinceTimestamp, noMdEntryTypes, noRelatedSym, some_bind] <;> rfl

theorem MarketDataRequest.taken (record : MarketDataRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 52] record.marketDepth (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 54, 53] record.mDUpdateType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 49] record.deribitSkipBlockTrades (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 50] record.deribitShowBlockTradeId (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 55] record.deribitTradeAmount (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 48, 56] record.deribitSinceTimestamp (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [50, 54, 55] NoMdEntryTypes.members NoMdEntryTypes.encode NoMdEntryTypes.within (by decide) (by decide) NoMdEntryTypes.taken record.noMdEntryTypes)
           (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
            (paired_none pairing))))))))))

structure NoQuoteSets where
  quoteSetID : Terminated 1  -- tag 302
  totNoQuoteEntries : Option (Terminated 1)  -- tag 304
  noQuoteEntries : Terminated 1  -- tag 295
  quoteEntryID : Terminated 1  -- tag 299
  symbol : Terminated 1  -- tag 55
  bidPx : Option (Terminated 1)  -- tag 132
  offerPx : Option (Terminated 1)  -- tag 133
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135
  execInst : Option (Terminated 1)  -- tag 18

def NoQuoteSets.parts (record : NoQuoteSets) : List Part :=
  [Part.required [51, 48, 50] record.quoteSetID,
   Part.optional [51, 48, 52] record.totNoQuoteEntries,
   Part.required [50, 57, 53] record.noQuoteEntries,
   Part.required [50, 57, 57] record.quoteEntryID,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [49, 56] record.execInst]

def NoQuoteSets.tags : List (List (List UInt8)) :=
  [[[51, 48, 50]], [[51, 48, 52]], [[50, 57, 53]], [[50, 57, 57]], [[53, 53]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]], [[49, 56]]]

theorem NoQuoteSets.shape (record : NoQuoteSets) : record.parts.map Part.tags = NoQuoteSets.tags := rfl

def NoQuoteSets.decode (tokens : List Token) : Option NoQuoteSets := do
  let quoteSetID ← readRequired [51, 48, 50] tokens
  let totNoQuoteEntries ← readOptional [51, 48, 52] tokens
  let noQuoteEntries ← readRequired [50, 57, 53] tokens
  let quoteEntryID ← readRequired [50, 57, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  pure { quoteSetID, totNoQuoteEntries, noQuoteEntries, quoteEntryID, symbol, bidPx, offerPx, bidSize, offerSize, execInst }

theorem NoQuoteSets.decode_agrees (record : NoQuoteSets) (tokens : List Token)
    (agrees : ∀ tags ∈ NoQuoteSets.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoQuoteSets.decode tokens = some record := by
  have distinct : NoQuoteSets.tags.flatten.Nodup := by decide +kernel
  have quoteSetID := readRequired_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have totNoQuoteEntries := readOptional_part [51, 48, 52] record.totNoQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noQuoteEntries := readRequired_part [50, 57, 53] record.noQuoteEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have quoteEntryID := readRequired_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [NoQuoteSets.decode, quoteSetID, totNoQuoteEntries, noQuoteEntries, quoteEntryID, symbol, bidPx, offerPx, bidSize, offerSize, execInst, some_bind] <;> rfl

theorem NoQuoteSets.taken (record : NoQuoteSets) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 48, 52] record.totNoQuoteEntries (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 57, 53] record.noQuoteEntries (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [50, 57, 57] record.quoteEntryID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50] record.bidPx (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 51, 51] record.offerPx (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 51, 52] record.bidSize (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 51, 53] record.offerSize (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
            (paired_none pairing))))))))))

def NoQuoteSets.members : List (List UInt8) := NoQuoteSets.tags.flatten

def NoQuoteSets.encode (entry : NoQuoteSets) : List Token := encodeParts entry.parts

theorem NoQuoteSets.decode_encode (entry : NoQuoteSets) : NoQuoteSets.decode entry.encode = some entry :=
  NoQuoteSets.decode_agrees entry _ (fun _ _ => rfl)

theorem NoQuoteSets.within (entry : NoQuoteSets) : ∀ token ∈ entry.encode, token.tag ∈ NoQuoteSets.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoQuoteSets.shape] at this

theorem NoQuoteSets.led (entry : NoQuoteSets) : Lead [51, 48, 50] entry.encode :=
  lead_parts [51, 48, 50] entry.quoteSetID _ NoQuoteSets.tags.tail rfl (by decide +kernel)

structure MassQuote where
  quoteID : Terminated 1  -- tag 117
  mMPGroup : Terminated 1  -- tag 9019
  validUntilTime : Option (Terminated 1)  -- tag 62
  noQuoteSets : List NoQuoteSets  -- tag 296

def MassQuote.parts (record : MassQuote) : List Part :=
  [Part.required [49, 49, 55] record.quoteID,
   Part.required [57, 48, 49, 57] record.mMPGroup,
   Part.optional [54, 50] record.validUntilTime,
   Part.group [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within record.noQuoteSets]

def MassQuote.tags : List (List (List UInt8)) :=
  [[[49, 49, 55]], [[57, 48, 49, 57]], [[54, 50]], [50, 57, 54] :: NoQuoteSets.members]

theorem MassQuote.shape (record : MassQuote) : record.parts.map Part.tags = MassQuote.tags := rfl

def MassQuote.decode (tokens : List Token) : Option MassQuote := do
  let quoteID ← readRequired [49, 49, 55] tokens
  let mMPGroup ← readRequired [57, 48, 49, 57] tokens
  let validUntilTime ← readOptional [54, 50] tokens
  let noQuoteSets ← readGroup [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.decode tokens
  pure { quoteID, mMPGroup, validUntilTime, noQuoteSets }

theorem MassQuote.decode_agrees (record : MassQuote) (tokens : List Token)
    (agrees : ∀ tags ∈ MassQuote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MassQuote.decode tokens = some record := by
  have distinct : MassQuote.tags.flatten.Nodup := by decide +kernel
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mMPGroup := readRequired_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have validUntilTime := readOptional_part [54, 50] record.validUntilTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noQuoteSets := readGroup_part [50, 57, 54] [51, 48, 50] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within NoQuoteSets.decode NoQuoteSets.decode_encode NoQuoteSets.led record.noQuoteSets tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [MassQuote.decode, quoteID, mMPGroup, validUntilTime, noQuoteSets, some_bind] <;> rfl

theorem MassQuote.taken (record : MassQuote) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 50] record.validUntilTime (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [50, 57, 54] NoQuoteSets.members NoQuoteSets.encode NoQuoteSets.within (by decide) (by decide) NoQuoteSets.taken record.noQuoteSets)
      (paired_none pairing))))

structure MMProtectionLimits where
  protectionRequestID : Terminated 1  -- tag 20114
  currency : Terminated 1  -- tag 15
  secondaryCurrency : Option (Terminated 1)  -- tag 5544
  protectionQtyLimit : Option (Terminated 1)  -- tag 20110
  protectionDeltaLimit : Option (Terminated 1)  -- tag 20111
  frozenLimit : Terminated 1  -- tag 20112
  intervalLength : Terminated 1  -- tag 20116
  protectionVegaLimit : Option (Terminated 1)  -- tag 20118
  maxQuoteQuantity : Option (Terminated 1)  -- tag 20119
  mMPGroup : Option (Terminated 1)  -- tag 9019

def MMProtectionLimits.parts (record : MMProtectionLimits) : List Part :=
  [Part.required [50, 48, 49, 49, 52] record.protectionRequestID,
   Part.required [49, 53] record.currency,
   Part.optional [53, 53, 52, 52] record.secondaryCurrency,
   Part.optional [50, 48, 49, 49, 48] record.protectionQtyLimit,
   Part.optional [50, 48, 49, 49, 49] record.protectionDeltaLimit,
   Part.required [50, 48, 49, 49, 50] record.frozenLimit,
   Part.required [50, 48, 49, 49, 54] record.intervalLength,
   Part.optional [50, 48, 49, 49, 56] record.protectionVegaLimit,
   Part.optional [50, 48, 49, 49, 57] record.maxQuoteQuantity,
   Part.optional [57, 48, 49, 57] record.mMPGroup]

def MMProtectionLimits.tags : List (List (List UInt8)) :=
  [[[50, 48, 49, 49, 52]], [[49, 53]], [[53, 53, 52, 52]], [[50, 48, 49, 49, 48]], [[50, 48, 49, 49, 49]], [[50, 48, 49, 49, 50]], [[50, 48, 49, 49, 54]], [[50, 48, 49, 49, 56]], [[50, 48, 49, 49, 57]], [[57, 48, 49, 57]]]

theorem MMProtectionLimits.shape (record : MMProtectionLimits) : record.parts.map Part.tags = MMProtectionLimits.tags := rfl

def MMProtectionLimits.decode (tokens : List Token) : Option MMProtectionLimits := do
  let protectionRequestID ← readRequired [50, 48, 49, 49, 52] tokens
  let currency ← readRequired [49, 53] tokens
  let secondaryCurrency ← readOptional [53, 53, 52, 52] tokens
  let protectionQtyLimit ← readOptional [50, 48, 49, 49, 48] tokens
  let protectionDeltaLimit ← readOptional [50, 48, 49, 49, 49] tokens
  let frozenLimit ← readRequired [50, 48, 49, 49, 50] tokens
  let intervalLength ← readRequired [50, 48, 49, 49, 54] tokens
  let protectionVegaLimit ← readOptional [50, 48, 49, 49, 56] tokens
  let maxQuoteQuantity ← readOptional [50, 48, 49, 49, 57] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  pure { protectionRequestID, currency, secondaryCurrency, protectionQtyLimit, protectionDeltaLimit, frozenLimit, intervalLength, protectionVegaLimit, maxQuoteQuantity, mMPGroup }

theorem MMProtectionLimits.decode_agrees (record : MMProtectionLimits) (tokens : List Token)
    (agrees : ∀ tags ∈ MMProtectionLimits.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MMProtectionLimits.decode tokens = some record := by
  have distinct : MMProtectionLimits.tags.flatten.Nodup := by decide +kernel
  have protectionRequestID := readRequired_part [50, 48, 49, 49, 52] record.protectionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryCurrency := readOptional_part [53, 53, 52, 52] record.secondaryCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have protectionQtyLimit := readOptional_part [50, 48, 49, 49, 48] record.protectionQtyLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have protectionDeltaLimit := readOptional_part [50, 48, 49, 49, 49] record.protectionDeltaLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have frozenLimit := readRequired_part [50, 48, 49, 49, 50] record.frozenLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have intervalLength := readRequired_part [50, 48, 49, 49, 54] record.intervalLength tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have protectionVegaLimit := readOptional_part [50, 48, 49, 49, 56] record.protectionVegaLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maxQuoteQuantity := readOptional_part [50, 48, 49, 49, 57] record.maxQuoteQuantity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [MMProtectionLimits.decode, protectionRequestID, currency, secondaryCurrency, protectionQtyLimit, protectionDeltaLimit, frozenLimit, intervalLength, protectionVegaLimit, maxQuoteQuantity, mMPGroup, some_bind] <;> rfl

theorem MMProtectionLimits.taken (record : MMProtectionLimits) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 52] record.protectionRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52, 52] record.secondaryCurrency (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 48] record.protectionQtyLimit (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 49] record.protectionDeltaLimit (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 50] record.frozenLimit (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 54] record.intervalLength (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 56] record.protectionVegaLimit (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49, 49, 57] record.maxQuoteQuantity (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
            (paired_none pairing))))))))))

structure MMProtectionReset where
  protectionRequestID : Terminated 1  -- tag 20114
  currency : Terminated 1  -- tag 15
  secondaryCurrency : Option (Terminated 1)  -- tag 5544
  mMPGroup : Option (Terminated 1)  -- tag 9019

def MMProtectionReset.parts (record : MMProtectionReset) : List Part :=
  [Part.required [50, 48, 49, 49, 52] record.protectionRequestID,
   Part.required [49, 53] record.currency,
   Part.optional [53, 53, 52, 52] record.secondaryCurrency,
   Part.optional [57, 48, 49, 57] record.mMPGroup]

def MMProtectionReset.tags : List (List (List UInt8)) :=
  [[[50, 48, 49, 49, 52]], [[49, 53]], [[53, 53, 52, 52]], [[57, 48, 49, 57]]]

theorem MMProtectionReset.shape (record : MMProtectionReset) : record.parts.map Part.tags = MMProtectionReset.tags := rfl

def MMProtectionReset.decode (tokens : List Token) : Option MMProtectionReset := do
  let protectionRequestID ← readRequired [50, 48, 49, 49, 52] tokens
  let currency ← readRequired [49, 53] tokens
  let secondaryCurrency ← readOptional [53, 53, 52, 52] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  pure { protectionRequestID, currency, secondaryCurrency, mMPGroup }

theorem MMProtectionReset.decode_agrees (record : MMProtectionReset) (tokens : List Token)
    (agrees : ∀ tags ∈ MMProtectionReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MMProtectionReset.decode tokens = some record := by
  have distinct : MMProtectionReset.tags.flatten.Nodup := by decide +kernel
  have protectionRequestID := readRequired_part [50, 48, 49, 49, 52] record.protectionRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryCurrency := readOptional_part [53, 53, 52, 52] record.secondaryCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [MMProtectionReset.decode, protectionRequestID, currency, secondaryCurrency, mMPGroup, some_bind] <;> rfl

theorem MMProtectionReset.taken (record : MMProtectionReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 48, 49, 49, 52] record.protectionRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52, 52] record.secondaryCurrency (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
      (paired_none pairing))))

structure NoFills where
  fillExecID : Terminated 1  -- tag 1363
  fillPx : Option (Terminated 1)  -- tag 1364
  fillQty : Option (Terminated 1)  -- tag 1365
  fillLiquidityInd : Option (Terminated 1)  -- tag 1443

def NoFills.parts (record : NoFills) : List Part :=
  [Part.required [49, 51, 54, 51] record.fillExecID,
   Part.optional [49, 51, 54, 52] record.fillPx,
   Part.optional [49, 51, 54, 53] record.fillQty,
   Part.optional [49, 52, 52, 51] record.fillLiquidityInd]

def NoFills.tags : List (List (List UInt8)) :=
  [[[49, 51, 54, 51]], [[49, 51, 54, 52]], [[49, 51, 54, 53]], [[49, 52, 52, 51]]]

theorem NoFills.shape (record : NoFills) : record.parts.map Part.tags = NoFills.tags := rfl

def NoFills.decode (tokens : List Token) : Option NoFills := do
  let fillExecID ← readRequired [49, 51, 54, 51] tokens
  let fillPx ← readOptional [49, 51, 54, 52] tokens
  let fillQty ← readOptional [49, 51, 54, 53] tokens
  let fillLiquidityInd ← readOptional [49, 52, 52, 51] tokens
  pure { fillExecID, fillPx, fillQty, fillLiquidityInd }

theorem NoFills.decode_agrees (record : NoFills) (tokens : List Token)
    (agrees : ∀ tags ∈ NoFills.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoFills.decode tokens = some record := by
  have distinct : NoFills.tags.flatten.Nodup := by decide +kernel
  have fillExecID := readRequired_part [49, 51, 54, 51] record.fillExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have fillPx := readOptional_part [49, 51, 54, 52] record.fillPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have fillQty := readOptional_part [49, 51, 54, 53] record.fillQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have fillLiquidityInd := readOptional_part [49, 52, 52, 51] record.fillLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoFills.decode, fillExecID, fillPx, fillQty, fillLiquidityInd, some_bind] <;> rfl

theorem NoFills.taken (record : NoFills) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 51] record.fillExecID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 51, 54, 52] record.fillPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 51, 54, 53] record.fillQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 52, 51] record.fillLiquidityInd (by decide) (by decide))
      (paired_none pairing))))

def NoFills.members : List (List UInt8) := NoFills.tags.flatten

def NoFills.encode (entry : NoFills) : List Token := encodeParts entry.parts

theorem NoFills.decode_encode (entry : NoFills) : NoFills.decode entry.encode = some entry :=
  NoFills.decode_agrees entry _ (fun _ _ => rfl)

theorem NoFills.within (entry : NoFills) : ∀ token ∈ entry.encode, token.tag ∈ NoFills.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoFills.shape] at this

theorem NoFills.led (entry : NoFills) : Lead [49, 51, 54, 51] entry.encode :=
  lead_parts [49, 51, 54, 51] entry.fillExecID _ NoFills.tags.tail rfl (by decide +kernel)

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  price : Terminated 1  -- tag 44
  symbol : Terminated 1  -- tag 55
  validUntilTime : Option (Terminated 1)  -- tag 62
  execInst : Option (Terminated 1)  -- tag 18
  ordType : Option (Terminated 1)  -- tag 40
  timeInForce : Option (Terminated 1)  -- tag 59
  stopPx : Option (Terminated 1)  -- tag 99
  displayQty : Option (Terminated 1)  -- tag 1138
  refreshQty : Option (Terminated 1)  -- tag 1088
  qtyType : Option (Terminated 1)  -- tag 854
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  pegPriceType : Option (Terminated 1)  -- tag 1094
  deribitLabel : Option (Terminated 1)  -- tag 100010
  deribitAdvOrderType : Option (Terminated 1)  -- tag 100012
  deribitMMProtection : Option (Terminated 1)  -- tag 9008
  conditionTriggerMethod : Option (Terminated 1)  -- tag 5127
  secondaryExecID : Option (Terminated 1)  -- tag 527
  orderId : Option (Terminated 1)  -- tag 37
  origClOrdId : Option (Terminated 1)  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  transactTime : Terminated 1  -- tag 60
  commission : Option (Terminated 1)  -- tag 12
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  execType : Option (Terminated 1)  -- tag 150
  ordRejReason : Terminated 1  -- tag 103
  text : Option (Terminated 1)  -- tag 58
  securityExchange : Option (Terminated 1)  -- tag 207
  contractMultiplier : Option (Terminated 1)  -- tag 231
  avgPx : Option (Terminated 1)  -- tag 6
  volatility : Option (Terminated 1)  -- tag 1188
  peggedPrice : Option (Terminated 1)  -- tag 839
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  mMPGroup : Option (Terminated 1)  -- tag 9019
  isLiquidation : Option (Terminated 1)  -- tag 9034
  isRebalance : Option (Terminated 1)  -- tag 9035
  isRiskReducing : Option (Terminated 1)  -- tag 9036
  quoteSetID : Option (Terminated 1)  -- tag 302
  quoteID : Option (Terminated 1)  -- tag 117
  quoteEntryID : Option (Terminated 1)  -- tag 299
  noFills : List NoFills  -- tag 1362

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 52] record.price,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 50] record.validUntilTime,
   Part.optional [49, 56] record.execInst,
   Part.optional [52, 48] record.ordType,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 56] record.refreshQty,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [49, 48, 57, 52] record.pegPriceType,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType,
   Part.optional [57, 48, 48, 56] record.deribitMMProtection,
   Part.optional [53, 49, 50, 55] record.conditionTriggerMethod,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [51, 55] record.orderId,
   Part.optional [52, 49] record.origClOrdId,
   Part.required [51, 57] record.ordStatus,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 50] record.commission,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.optional [49, 53, 48] record.execType,
   Part.required [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49, 56, 56] record.volatility,
   Part.optional [56, 51, 57] record.peggedPrice,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [57, 48, 49, 57] record.mMPGroup,
   Part.optional [57, 48, 51, 52] record.isLiquidation,
   Part.optional [57, 48, 51, 53] record.isRebalance,
   Part.optional [57, 48, 51, 54] record.isRiskReducing,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [49, 49, 55] record.quoteID,
   Part.optional [50, 57, 57] record.quoteEntryID,
   Part.group [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within record.noFills]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 52]], [[51, 56]], [[52, 52]], [[53, 53]], [[54, 50]], [[49, 56]], [[52, 48]], [[53, 57]], [[57, 57]], [[49, 49, 51, 56]], [[49, 48, 56, 56]], [[56, 53, 52]], [[50, 49, 49]], [[49, 48, 57, 52]], [[49, 48, 48, 48, 49, 48]], [[49, 48, 48, 48, 49, 50]], [[57, 48, 48, 56]], [[53, 49, 50, 55]], [[53, 50, 55]], [[51, 55]], [[52, 49]], [[51, 57]], [[54, 48]], [[49, 50]], [[49, 53, 49]], [[49, 52]], [[49, 53, 48]], [[49, 48, 51]], [[53, 56]], [[50, 48, 55]], [[50, 51, 49]], [[54]], [[49, 49, 56, 56]], [[56, 51, 57]], [[51, 49]], [[51, 50]], [[57, 48, 49, 57]], [[57, 48, 51, 52]], [[57, 48, 51, 53]], [[57, 48, 51, 54]], [[51, 48, 50]], [[49, 49, 55]], [[50, 57, 57]], [49, 51, 54, 50] :: NoFills.members]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let price ← readRequired [52, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let validUntilTime ← readOptional [54, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let refreshQty ← readOptional [49, 48, 56, 56] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let pegPriceType ← readOptional [49, 48, 57, 52] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let deribitAdvOrderType ← readOptional [49, 48, 48, 48, 49, 50] tokens
  let deribitMMProtection ← readOptional [57, 48, 48, 56] tokens
  let conditionTriggerMethod ← readOptional [53, 49, 50, 55] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let orderId ← readOptional [51, 55] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let commission ← readOptional [49, 50] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let ordRejReason ← readRequired [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let avgPx ← readOptional [54] tokens
  let volatility ← readOptional [49, 49, 56, 56] tokens
  let peggedPrice ← readOptional [56, 51, 57] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  let isLiquidation ← readOptional [57, 48, 51, 52] tokens
  let isRebalance ← readOptional [57, 48, 51, 53] tokens
  let isRiskReducing ← readOptional [57, 48, 51, 54] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteEntryID ← readOptional [50, 57, 57] tokens
  let noFills ← readGroup [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.decode tokens
  pure { clOrdID, side, orderQty, price, symbol, validUntilTime, execInst, ordType, timeInForce, stopPx, displayQty, refreshQty, qtyType, pegOffsetValue, pegPriceType, deribitLabel, deribitAdvOrderType, deribitMMProtection, conditionTriggerMethod, secondaryExecID, orderId, origClOrdId, ordStatus, transactTime, commission, leavesQty, cumQty, execType, ordRejReason, text, securityExchange, contractMultiplier, avgPx, volatility, peggedPrice, lastPx, lastQty, mMPGroup, isLiquidation, isRebalance, isRiskReducing, quoteSetID, quoteID, quoteEntryID, noFills }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have validUntilTime := readOptional_part [54, 50] record.validUntilTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have refreshQty := readOptional_part [49, 48, 56, 56] record.refreshQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have pegPriceType := readOptional_part [49, 48, 57, 52] record.pegPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have deribitAdvOrderType := readOptional_part [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have deribitMMProtection := readOptional_part [57, 48, 48, 56] record.deribitMMProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have conditionTriggerMethod := readOptional_part [53, 49, 50, 55] record.conditionTriggerMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have volatility := readOptional_part [49, 49, 56, 56] record.volatility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have peggedPrice := readOptional_part [56, 51, 57] record.peggedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have isLiquidation := readOptional_part [57, 48, 51, 52] record.isLiquidation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have isRebalance := readOptional_part [57, 48, 51, 53] record.isRebalance tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have isRiskReducing := readOptional_part [57, 48, 51, 54] record.isRiskReducing tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have quoteEntryID := readOptional_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have noFills := readGroup_part [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.encode NoFills.within NoFills.decode NoFills.decode_encode NoFills.led record.noFills tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, side, orderQty, price, symbol, validUntilTime, execInst, ordType, timeInForce, stopPx, displayQty, refreshQty, qtyType, pegOffsetValue, pegPriceType, deribitLabel, deribitAdvOrderType, deribitMMProtection, conditionTriggerMethod, secondaryExecID, orderId, origClOrdId, ordStatus, transactTime, commission, leavesQty, cumQty, execType, ordRejReason, text, securityExchange, contractMultiplier, avgPx, volatility, peggedPrice, lastPx, lastQty, mMPGroup, isLiquidation, isRebalance, isRiskReducing, quoteSetID, quoteID, quoteEntryID, noFills, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 50] record.validUntilTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 56] record.refreshQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [56, 53, 52] record.qtyType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffsetValue (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57, 52] record.pegPriceType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 56] record.deribitMMProtection (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [53, 49, 50, 55] record.conditionTriggerMethod (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [53, 50, 55] record.secondaryExecID (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 50] record.commission (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_required pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [54] record.avgPx (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [49, 49, 56, 56] record.volatility (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [56, 51, 57] record.peggedPrice (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 52] record.isLiquidation (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 53] record.isRebalance (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 54] record.isRiskReducing (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 55] record.quoteID (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [50, 57, 57] record.quoteEntryID (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_group pairing [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within (by decide) (by decide) NoFills.taken record.noFills)
                                               (paired_none pairing)))))))))))))))))))))))))))))))))))))))))))))

structure OrderCancelReplaceRequest where
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdId : Option (Terminated 1)  -- tag 41
  deribitLabel : Option (Terminated 1)  -- tag 100010
  symbol : Terminated 1  -- tag 55
  validUntilTime : Option (Terminated 1)  -- tag 62
  currency : Option (Terminated 1)  -- tag 15
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  execInst : Option (Terminated 1)  -- tag 18
  qtyType : Option (Terminated 1)  -- tag 854
  displayQty : Option (Terminated 1)  -- tag 1138
  deribitMMProtection : Option (Terminated 1)  -- tag 9008

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdId,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.required [53, 53] record.symbol,
   Part.optional [54, 50] record.validUntilTime,
   Part.optional [49, 53] record.currency,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 56] record.execInst,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [57, 48, 48, 56] record.deribitMMProtection]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[49, 48, 48, 48, 49, 48]], [[53, 53]], [[54, 50]], [[49, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 56]], [[56, 53, 52]], [[49, 49, 51, 56]], [[57, 48, 48, 56]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  let validUntilTime ← readOptional [54, 50] tokens
  let currency ← readOptional [49, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let execInst ← readOptional [49, 56] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let deribitMMProtection ← readOptional [57, 48, 48, 56] tokens
  pure { clOrdID, origClOrdId, deribitLabel, symbol, validUntilTime, currency, side, orderQty, ordType, price, execInst, qtyType, displayQty, deribitMMProtection }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have validUntilTime := readOptional_part [54, 50] record.validUntilTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have deribitMMProtection := readOptional_part [57, 48, 48, 56] record.deribitMMProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, clOrdID, origClOrdId, deribitLabel, symbol, validUntilTime, currency, side, orderQty, ordType, price, execInst, qtyType, displayQty, deribitMMProtection, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 50] record.validUntilTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [56, 53, 52] record.qtyType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 56] record.deribitMMProtection (by decide) (by decide))
                (paired_none pairing))))))))))))))

structure OrderCancelRequest where
  clOrdID : Option (Terminated 1)  -- tag 11
  origClOrdId : Option (Terminated 1)  -- tag 41
  deribitLabel : Option (Terminated 1)  -- tag 100010
  symbol : Option (Terminated 1)  -- tag 55
  currency : Option (Terminated 1)  -- tag 15

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 49] record.origClOrdId,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 53] record.currency]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[52, 49]], [[49, 48, 48, 48, 49, 48]], [[53, 53]], [[49, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readOptional [49, 49] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let currency ← readOptional [49, 53] tokens
  pure { clOrdID, origClOrdId, deribitLabel, symbol, currency }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, origClOrdId, deribitLabel, symbol, currency, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
       (paired_none pairing)))))

structure OrderMassCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  deribitLabel : Option (Terminated 1)  -- tag 100010
  securityType : Option (Terminated 1)  -- tag 167
  symbol : Option (Terminated 1)  -- tag 55
  currency : Option (Terminated 1)  -- tag 15
  freezeQuotes : Option (Terminated 1)  -- tag 9031

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 53] record.currency,
   Part.optional [57, 48, 51, 49] record.freezeQuotes]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 51, 48]], [[49, 48, 48, 48, 49, 48]], [[49, 54, 55]], [[53, 53]], [[49, 53]], [[57, 48, 51, 49]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let currency ← readOptional [49, 53] tokens
  let freezeQuotes ← readOptional [57, 48, 51, 49] tokens
  pure { clOrdID, massCancelRequestType, deribitLabel, securityType, symbol, currency, freezeQuotes }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have freezeQuotes := readOptional_part [57, 48, 51, 49] record.freezeQuotes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, clOrdID, massCancelRequestType, deribitLabel, securityType, symbol, currency, freezeQuotes, some_bind] <;> rfl

theorem OrderMassCancelRequest.taken (record : OrderMassCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.massCancelRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 49] record.freezeQuotes (by decide) (by decide))
         (paired_none pairing)))))))

structure OrderMassStatusRequest where
  massStatusReqID : Terminated 1  -- tag 584
  massStatusReqType : Terminated 1  -- tag 585
  massStatusReqIDType : Option (Terminated 1)  -- tag 9014
  currency : Option (Terminated 1)  -- tag 15
  symbol : Option (Terminated 1)  -- tag 55
  orderId : Option (Terminated 1)  -- tag 37
  origClOrdId : Option (Terminated 1)  -- tag 41
  ordStatus : Terminated 1  -- tag 39
  side : Terminated 1  -- tag 54
  transactTime : Terminated 1  -- tag 60
  commission : Option (Terminated 1)  -- tag 12
  leavesQty : Terminated 1  -- tag 151
  cumQty : Terminated 1  -- tag 14
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Terminated 1  -- tag 44
  execType : Option (Terminated 1)  -- tag 150
  execInst : Option (Terminated 1)  -- tag 18
  ordRejReason : Terminated 1  -- tag 103
  text : Option (Terminated 1)  -- tag 58
  securityExchange : Option (Terminated 1)  -- tag 207
  qtyType : Option (Terminated 1)  -- tag 854
  contractMultiplier : Option (Terminated 1)  -- tag 231
  avgPx : Option (Terminated 1)  -- tag 6
  displayQty : Option (Terminated 1)  -- tag 1138
  deribitMMProtection : Option (Terminated 1)  -- tag 9008
  deribitAdvOrderType : Option (Terminated 1)  -- tag 100012
  volatility : Option (Terminated 1)  -- tag 1188
  peggedPrice : Option (Terminated 1)  -- tag 839
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  deribitLabel : Option (Terminated 1)  -- tag 100010
  mMPGroup : Option (Terminated 1)  -- tag 9019
  quoteSetID : Option (Terminated 1)  -- tag 302
  quoteID : Option (Terminated 1)  -- tag 117
  quoteEntryID : Option (Terminated 1)  -- tag 299
  noFills : List NoFills  -- tag 1362
  totNumReports : Terminated 1  -- tag 911

def OrderMassStatusRequest.parts (record : OrderMassStatusRequest) : List Part :=
  [Part.required [53, 56, 52] record.massStatusReqID,
   Part.required [53, 56, 53] record.massStatusReqType,
   Part.optional [57, 48, 49, 52] record.massStatusReqIDType,
   Part.optional [49, 53] record.currency,
   Part.optional [53, 53] record.symbol,
   Part.optional [51, 55] record.orderId,
   Part.optional [52, 49] record.origClOrdId,
   Part.required [51, 57] record.ordStatus,
   Part.required [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 50] record.commission,
   Part.required [49, 53, 49] record.leavesQty,
   Part.required [49, 52] record.cumQty,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 52] record.price,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [49, 56] record.execInst,
   Part.required [49, 48, 51] record.ordRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [56, 53, 52] record.qtyType,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [54] record.avgPx,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [57, 48, 48, 56] record.deribitMMProtection,
   Part.optional [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType,
   Part.optional [49, 49, 56, 56] record.volatility,
   Part.optional [56, 51, 57] record.peggedPrice,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.optional [49, 48, 48, 48, 49, 48] record.deribitLabel,
   Part.optional [57, 48, 49, 57] record.mMPGroup,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [49, 49, 55] record.quoteID,
   Part.optional [50, 57, 57] record.quoteEntryID,
   Part.group [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within record.noFills,
   Part.required [57, 49, 49] record.totNumReports]

def OrderMassStatusRequest.tags : List (List (List UInt8)) :=
  [[[53, 56, 52]], [[53, 56, 53]], [[57, 48, 49, 52]], [[49, 53]], [[53, 53]], [[51, 55]], [[52, 49]], [[51, 57]], [[53, 52]], [[54, 48]], [[49, 50]], [[49, 53, 49]], [[49, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 53, 48]], [[49, 56]], [[49, 48, 51]], [[53, 56]], [[50, 48, 55]], [[56, 53, 52]], [[50, 51, 49]], [[54]], [[49, 49, 51, 56]], [[57, 48, 48, 56]], [[49, 48, 48, 48, 49, 50]], [[49, 49, 56, 56]], [[56, 51, 57]], [[51, 49]], [[51, 50]], [[49, 48, 48, 48, 49, 48]], [[57, 48, 49, 57]], [[51, 48, 50]], [[49, 49, 55]], [[50, 57, 57]], [49, 51, 54, 50] :: NoFills.members, [[57, 49, 49]]]

theorem OrderMassStatusRequest.shape (record : OrderMassStatusRequest) : record.parts.map Part.tags = OrderMassStatusRequest.tags := rfl

def OrderMassStatusRequest.decode (tokens : List Token) : Option OrderMassStatusRequest := do
  let massStatusReqID ← readRequired [53, 56, 52] tokens
  let massStatusReqType ← readRequired [53, 56, 53] tokens
  let massStatusReqIDType ← readOptional [57, 48, 49, 52] tokens
  let currency ← readOptional [49, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let orderId ← readOptional [51, 55] tokens
  let origClOrdId ← readOptional [52, 49] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let side ← readRequired [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let commission ← readOptional [49, 50] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let cumQty ← readRequired [49, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readRequired [52, 52] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let execInst ← readOptional [49, 56] tokens
  let ordRejReason ← readRequired [49, 48, 51] tokens
  let text ← readOptional [53, 56] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let qtyType ← readOptional [56, 53, 52] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let avgPx ← readOptional [54] tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let deribitMMProtection ← readOptional [57, 48, 48, 56] tokens
  let deribitAdvOrderType ← readOptional [49, 48, 48, 48, 49, 50] tokens
  let volatility ← readOptional [49, 49, 56, 56] tokens
  let peggedPrice ← readOptional [56, 51, 57] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let deribitLabel ← readOptional [49, 48, 48, 48, 49, 48] tokens
  let mMPGroup ← readOptional [57, 48, 49, 57] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let quoteID ← readOptional [49, 49, 55] tokens
  let quoteEntryID ← readOptional [50, 57, 57] tokens
  let noFills ← readGroup [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.decode tokens
  let totNumReports ← readRequired [57, 49, 49] tokens
  pure { massStatusReqID, massStatusReqType, massStatusReqIDType, currency, symbol, orderId, origClOrdId, ordStatus, side, transactTime, commission, leavesQty, cumQty, orderQty, ordType, price, execType, execInst, ordRejReason, text, securityExchange, qtyType, contractMultiplier, avgPx, displayQty, deribitMMProtection, deribitAdvOrderType, volatility, peggedPrice, lastPx, lastQty, deribitLabel, mMPGroup, quoteSetID, quoteID, quoteEntryID, noFills, totNumReports }

theorem OrderMassStatusRequest.decode_agrees (record : OrderMassStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassStatusRequest.decode tokens = some record := by
  have distinct : OrderMassStatusRequest.tags.flatten.Nodup := by decide +kernel
  have massStatusReqID := readRequired_part [53, 56, 52] record.massStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massStatusReqType := readRequired_part [53, 56, 53] record.massStatusReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massStatusReqIDType := readOptional_part [57, 48, 49, 52] record.massStatusReqIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderId := readOptional_part [51, 55] record.orderId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdId := readOptional_part [52, 49] record.origClOrdId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have price := readRequired_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have ordRejReason := readRequired_part [49, 48, 51] record.ordRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have qtyType := readOptional_part [56, 53, 52] record.qtyType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have avgPx := readOptional_part [54] record.avgPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have deribitMMProtection := readOptional_part [57, 48, 48, 56] record.deribitMMProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have deribitAdvOrderType := readOptional_part [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have volatility := readOptional_part [49, 49, 56, 56] record.volatility tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have peggedPrice := readOptional_part [56, 51, 57] record.peggedPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have deribitLabel := readOptional_part [49, 48, 48, 48, 49, 48] record.deribitLabel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have mMPGroup := readOptional_part [57, 48, 49, 57] record.mMPGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have quoteID := readOptional_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have quoteEntryID := readOptional_part [50, 57, 57] record.quoteEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have noFills := readGroup_part [49, 51, 54, 50] [49, 51, 54, 51] NoFills.members NoFills.encode NoFills.within NoFills.decode NoFills.decode_encode NoFills.led record.noFills tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have totNumReports := readRequired_part [57, 49, 49] record.totNumReports tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  simp only [OrderMassStatusRequest.decode, massStatusReqID, massStatusReqType, massStatusReqIDType, currency, symbol, orderId, origClOrdId, ordStatus, side, transactTime, commission, leavesQty, cumQty, orderQty, ordType, price, execType, execInst, ordRejReason, text, securityExchange, qtyType, contractMultiplier, avgPx, displayQty, deribitMMProtection, deribitAdvOrderType, volatility, peggedPrice, lastPx, lastQty, deribitLabel, mMPGroup, quoteSetID, quoteID, quoteEntryID, noFills, totNumReports, some_bind] <;> rfl

theorem OrderMassStatusRequest.taken (record : OrderMassStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 56, 52] record.massStatusReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 56, 53] record.massStatusReqType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 52] record.massStatusReqIDType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderId (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdId (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 50] record.commission (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [52, 52] record.price (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48] record.execType (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [49, 48, 51] record.ordRejReason (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [56, 53, 52] record.qtyType (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [54] record.avgPx (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 56] record.deribitMMProtection (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 50] record.deribitAdvOrderType (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 56, 56] record.volatility (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [56, 51, 57] record.peggedPrice (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 48, 49, 48] record.deribitLabel (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 57] record.mMPGroup (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 55] record.quoteID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [50, 57, 57] record.quoteEntryID (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_group pairing [49, 51, 54, 50] NoFills.members NoFills.encode NoFills.within (by decide) (by decide) NoFills.taken record.noFills)
                                       (paired_cons pairing _ _ (paired_required pairing [57, 49, 49] record.totNumReports (by decide) (by decide))
                                        (paired_none pairing))))))))))))))))))))))))))))))))))))))

structure QuoteCancel where
  quoteMsgID : Option (Terminated 1)  -- tag 1166
  quoteCancelType : Option (Terminated 1)  -- tag 298
  symbol : Option (Terminated 1)  -- tag 55
  currency : Option (Terminated 1)  -- tag 15
  freezeQuotes : Option (Terminated 1)  -- tag 9031
  securityType : Option (Terminated 1)  -- tag 167
  quoteSetID : Option (Terminated 1)  -- tag 302
  minDelta : Option (Terminated 1)  -- tag 9032
  maxDelta : Option (Terminated 1)  -- tag 9033

def QuoteCancel.parts (record : QuoteCancel) : List Part :=
  [Part.optional [49, 49, 54, 54] record.quoteMsgID,
   Part.optional [50, 57, 56] record.quoteCancelType,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 53] record.currency,
   Part.optional [57, 48, 51, 49] record.freezeQuotes,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [51, 48, 50] record.quoteSetID,
   Part.optional [57, 48, 51, 50] record.minDelta,
   Part.optional [57, 48, 51, 51] record.maxDelta]

def QuoteCancel.tags : List (List (List UInt8)) :=
  [[[49, 49, 54, 54]], [[50, 57, 56]], [[53, 53]], [[49, 53]], [[57, 48, 51, 49]], [[49, 54, 55]], [[51, 48, 50]], [[57, 48, 51, 50]], [[57, 48, 51, 51]]]

theorem QuoteCancel.shape (record : QuoteCancel) : record.parts.map Part.tags = QuoteCancel.tags := rfl

def QuoteCancel.decode (tokens : List Token) : Option QuoteCancel := do
  let quoteMsgID ← readOptional [49, 49, 54, 54] tokens
  let quoteCancelType ← readOptional [50, 57, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let currency ← readOptional [49, 53] tokens
  let freezeQuotes ← readOptional [57, 48, 51, 49] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let quoteSetID ← readOptional [51, 48, 50] tokens
  let minDelta ← readOptional [57, 48, 51, 50] tokens
  let maxDelta ← readOptional [57, 48, 51, 51] tokens
  pure { quoteMsgID, quoteCancelType, symbol, currency, freezeQuotes, securityType, quoteSetID, minDelta, maxDelta }

theorem QuoteCancel.decode_agrees (record : QuoteCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteCancel.decode tokens = some record := by
  have distinct : QuoteCancel.tags.flatten.Nodup := by decide +kernel
  have quoteMsgID := readOptional_part [49, 49, 54, 54] record.quoteMsgID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have quoteCancelType := readOptional_part [50, 57, 56] record.quoteCancelType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have freezeQuotes := readOptional_part [57, 48, 51, 49] record.freezeQuotes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have quoteSetID := readOptional_part [51, 48, 50] record.quoteSetID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have minDelta := readOptional_part [57, 48, 51, 50] record.minDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maxDelta := readOptional_part [57, 48, 51, 51] record.maxDelta tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [QuoteCancel.decode, quoteMsgID, quoteCancelType, symbol, currency, freezeQuotes, securityType, quoteSetID, minDelta, maxDelta, some_bind] <;> rfl

theorem QuoteCancel.taken (record : QuoteCancel) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 54, 54] record.quoteMsgID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 57, 56] record.quoteCancelType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 49] record.freezeQuotes (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 48, 50] record.quoteSetID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 50] record.minDelta (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [57, 48, 51, 51] record.maxDelta (by decide) (by decide))
           (paired_none pairing)))))))))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refMsgType, sessionRejectReason, text }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

structure RequestForPositions where
  posReqID : Terminated 1  -- tag 710
  posReqType : Terminated 1  -- tag 724
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  currency : Option (Terminated 1)  -- tag 15

def RequestForPositions.parts (record : RequestForPositions) : List Part :=
  [Part.required [55, 49, 48] record.posReqID,
   Part.required [55, 50, 52] record.posReqType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [49, 53] record.currency]

def RequestForPositions.tags : List (List (List UInt8)) :=
  [[[55, 49, 48]], [[55, 50, 52]], [[50, 54, 51]], [[49, 53]]]

theorem RequestForPositions.shape (record : RequestForPositions) : record.parts.map Part.tags = RequestForPositions.tags := rfl

def RequestForPositions.decode (tokens : List Token) : Option RequestForPositions := do
  let posReqID ← readRequired [55, 49, 48] tokens
  let posReqType ← readRequired [55, 50, 52] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let currency ← readOptional [49, 53] tokens
  pure { posReqID, posReqType, subscriptionRequestType, currency }

theorem RequestForPositions.decode_agrees (record : RequestForPositions) (tokens : List Token)
    (agrees : ∀ tags ∈ RequestForPositions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    RequestForPositions.decode tokens = some record := by
  have distinct : RequestForPositions.tags.flatten.Nodup := by decide +kernel
  have posReqID := readRequired_part [55, 49, 48] record.posReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have posReqType := readRequired_part [55, 50, 52] record.posReqType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [RequestForPositions.decode, posReqID, posReqType, subscriptionRequestType, currency, some_bind] <;> rfl

theorem RequestForPositions.taken (record : RequestForPositions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55, 49, 48] record.posReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [55, 50, 52] record.posReqType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
      (paired_none pairing))))

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

theorem ResendRequest.taken (record : ResendRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [55] record.beginSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54] record.endSeqNo (by decide) (by decide))
    (paired_none pairing))

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSide : Option (Terminated 1)  -- tag 624
  legRatioQty : Option (Terminated 1)  -- tag 623

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [54, 50, 51] record.legRatioQty]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 50, 52]], [[54, 50, 51]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legRatioQty ← readOptional [54, 50, 51] tokens
  pure { legSymbol, legSide, legRatioQty }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legRatioQty := readOptional_part [54, 50, 51] record.legRatioQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSide, legRatioQty, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 50, 52] record.legSide (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 50, 51] record.legRatioQty (by decide) (by decide))
     (paired_none pairing)))

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

structure SecurityDefinitionRequest where
  securityReqID : Terminated 1  -- tag 320
  securityRequestType : Terminated 1  -- tag 321
  currency : Terminated 1  -- tag 15
  securityID : Option (Terminated 1)  -- tag 48
  noLegs : List NoLegs  -- tag 555

def SecurityDefinitionRequest.parts (record : SecurityDefinitionRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 49] record.securityRequestType,
   Part.required [49, 53] record.currency,
   Part.optional [52, 56] record.securityID,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinitionRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 49]], [[49, 53]], [[52, 56]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinitionRequest.shape (record : SecurityDefinitionRequest) : record.parts.map Part.tags = SecurityDefinitionRequest.tags := rfl

def SecurityDefinitionRequest.decode (tokens : List Token) : Option SecurityDefinitionRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityRequestType ← readRequired [51, 50, 49] tokens
  let currency ← readRequired [49, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityReqID, securityRequestType, currency, securityID, noLegs }

theorem SecurityDefinitionRequest.decode_agrees (record : SecurityDefinitionRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinitionRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinitionRequest.decode tokens = some record := by
  have distinct : SecurityDefinitionRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityRequestType := readRequired_part [51, 50, 49] record.securityRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [SecurityDefinitionRequest.decode, securityReqID, securityRequestType, currency, securityID, noLegs, some_bind] <;> rfl

theorem SecurityDefinitionRequest.taken (record : SecurityDefinitionRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 49] record.securityRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
       (paired_none pairing)))))

structure SecurityListRequest where
  securityReqID : Terminated 1  -- tag 320
  securityListRequestType : Terminated 1  -- tag 559
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  displayMulticastInstrumentID : Option (Terminated 1)  -- tag 9013
  displayIncrementSteps : Option (Terminated 1)  -- tag 9018
  currency : Option (Terminated 1)  -- tag 15
  secondaryCurrency : Option (Terminated 1)  -- tag 5544
  securityType : Option (Terminated 1)  -- tag 167

def SecurityListRequest.parts (record : SecurityListRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [53, 53, 57] record.securityListRequestType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [57, 48, 49, 51] record.displayMulticastInstrumentID,
   Part.optional [57, 48, 49, 56] record.displayIncrementSteps,
   Part.optional [49, 53] record.currency,
   Part.optional [53, 53, 52, 52] record.secondaryCurrency,
   Part.optional [49, 54, 55] record.securityType]

def SecurityListRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[53, 53, 57]], [[50, 54, 51]], [[57, 48, 49, 51]], [[57, 48, 49, 56]], [[49, 53]], [[53, 53, 52, 52]], [[49, 54, 55]]]

theorem SecurityListRequest.shape (record : SecurityListRequest) : record.parts.map Part.tags = SecurityListRequest.tags := rfl

def SecurityListRequest.decode (tokens : List Token) : Option SecurityListRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityListRequestType ← readRequired [53, 53, 57] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let displayMulticastInstrumentID ← readOptional [57, 48, 49, 51] tokens
  let displayIncrementSteps ← readOptional [57, 48, 49, 56] tokens
  let currency ← readOptional [49, 53] tokens
  let secondaryCurrency ← readOptional [53, 53, 52, 52] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  pure { securityReqID, securityListRequestType, subscriptionRequestType, displayMulticastInstrumentID, displayIncrementSteps, currency, secondaryCurrency, securityType }

theorem SecurityListRequest.decode_agrees (record : SecurityListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityListRequest.decode tokens = some record := by
  have distinct : SecurityListRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityListRequestType := readRequired_part [53, 53, 57] record.securityListRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have displayMulticastInstrumentID := readOptional_part [57, 48, 49, 51] record.displayMulticastInstrumentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have displayIncrementSteps := readOptional_part [57, 48, 49, 56] record.displayIncrementSteps tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have secondaryCurrency := readOptional_part [53, 53, 52, 52] record.secondaryCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [SecurityListRequest.decode, securityReqID, securityListRequestType, subscriptionRequestType, displayMulticastInstrumentID, displayIncrementSteps, currency, secondaryCurrency, securityType, some_bind] <;> rfl

theorem SecurityListRequest.taken (record : SecurityListRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53, 57] record.securityListRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 51] record.displayMulticastInstrumentID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [57, 48, 49, 56] record.displayIncrementSteps (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52, 52] record.secondaryCurrency (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
          (paired_none pairing))))))))

structure SecurityStatusRequest where
  securityStatusReqID : Terminated 1  -- tag 324
  symbol : Terminated 1  -- tag 55
  subscriptionRequestType : Terminated 1  -- tag 263

def SecurityStatusRequest.parts (record : SecurityStatusRequest) : List Part :=
  [Part.required [51, 50, 52] record.securityStatusReqID,
   Part.required [53, 53] record.symbol,
   Part.required [50, 54, 51] record.subscriptionRequestType]

def SecurityStatusRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 52]], [[53, 53]], [[50, 54, 51]]]

theorem SecurityStatusRequest.shape (record : SecurityStatusRequest) : record.parts.map Part.tags = SecurityStatusRequest.tags := rfl

def SecurityStatusRequest.decode (tokens : List Token) : Option SecurityStatusRequest := do
  let securityStatusReqID ← readRequired [51, 50, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  pure { securityStatusReqID, symbol, subscriptionRequestType }

theorem SecurityStatusRequest.decode_agrees (record : SecurityStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityStatusRequest.decode tokens = some record := by
  have distinct : SecurityStatusRequest.tags.flatten.Nodup := by decide +kernel
  have securityStatusReqID := readRequired_part [51, 50, 52] record.securityStatusReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [SecurityStatusRequest.decode, securityStatusReqID, symbol, subscriptionRequestType, some_bind] <;> rfl

theorem SecurityStatusRequest.taken (record : SecurityStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 52] record.securityStatusReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_none pairing)))

structure SequenceReset where
  newSeqNo : Terminated 1  -- tag 36

def SequenceReset.parts (record : SequenceReset) : List Part :=
  [Part.required [51, 54] record.newSeqNo]

def SequenceReset.tags : List (List (List UInt8)) :=
  [[[51, 54]]]

theorem SequenceReset.shape (record : SequenceReset) : record.parts.map Part.tags = SequenceReset.tags := rfl

def SequenceReset.decode (tokens : List Token) : Option SequenceReset := do
  let newSeqNo ← readRequired [51, 54] tokens
  pure { newSeqNo }

theorem SequenceReset.decode_agrees (record : SequenceReset) (tokens : List Token)
    (agrees : ∀ tags ∈ SequenceReset.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SequenceReset.decode tokens = some record := by
  have distinct : SequenceReset.tags.flatten.Nodup := by decide +kernel
  have newSeqNo := readRequired_part [51, 54] record.newSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [SequenceReset.decode, newSeqNo, some_bind] <;> rfl

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
   (paired_none pairing)

structure TestRequest where
  testReqId : Terminated 1  -- tag 112

def TestRequest.parts (record : TestRequest) : List Part :=
  [Part.required [49, 49, 50] record.testReqId]

def TestRequest.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem TestRequest.shape (record : TestRequest) : record.parts.map Part.tags = TestRequest.tags := rfl

def TestRequest.decode (tokens : List Token) : Option TestRequest := do
  let testReqId ← readRequired [49, 49, 50] tokens
  pure { testReqId }

theorem TestRequest.decode_agrees (record : TestRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TestRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TestRequest.decode tokens = some record := by
  have distinct : TestRequest.tags.flatten.Nodup := by decide +kernel
  have testReqId := readRequired_part [49, 49, 50] record.testReqId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [TestRequest.decode, testReqId, some_bind] <;> rfl

theorem TestRequest.taken (record : TestRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqId (by decide) (by decide))
   (paired_none pairing)

structure TradeCaptureReportRequest where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  symbol : Terminated 1  -- tag 55
  subscriptionRequestType : Option (Terminated 1)  -- tag 263

def TradeCaptureReportRequest.parts (record : TradeCaptureReportRequest) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.required [53, 53] record.symbol,
   Part.optional [50, 54, 51] record.subscriptionRequestType]

def TradeCaptureReportRequest.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[53, 53]], [[50, 54, 51]]]

theorem TradeCaptureReportRequest.shape (record : TradeCaptureReportRequest) : record.parts.map Part.tags = TradeCaptureReportRequest.tags := rfl

def TradeCaptureReportRequest.decode (tokens : List Token) : Option TradeCaptureReportRequest := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  pure { tradeRequestID, tradeRequestType, symbol, subscriptionRequestType }

theorem TradeCaptureReportRequest.decode_agrees (record : TradeCaptureReportRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportRequest.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TradeCaptureReportRequest.decode, tradeRequestID, tradeRequestType, symbol, subscriptionRequestType, some_bind] <;> rfl

theorem TradeCaptureReportRequest.taken (record : TradeCaptureReportRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54, 57] record.tradeRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
      (paired_none pairing))))

structure UserRequest where
  userRequestID : Terminated 1  -- tag 923
  userRequestType : Terminated 1  -- tag 924
  username : Terminated 1  -- tag 553
  currency : Option (Terminated 1)  -- tag 15

def UserRequest.parts (record : UserRequest) : List Part :=
  [Part.required [57, 50, 51] record.userRequestID,
   Part.required [57, 50, 52] record.userRequestType,
   Part.required [53, 53, 51] record.username,
   Part.optional [49, 53] record.currency]

def UserRequest.tags : List (List (List UInt8)) :=
  [[[57, 50, 51]], [[57, 50, 52]], [[53, 53, 51]], [[49, 53]]]

theorem UserRequest.shape (record : UserRequest) : record.parts.map Part.tags = UserRequest.tags := rfl

def UserRequest.decode (tokens : List Token) : Option UserRequest := do
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userRequestType ← readRequired [57, 50, 52] tokens
  let username ← readRequired [53, 53, 51] tokens
  let currency ← readOptional [49, 53] tokens
  pure { userRequestID, userRequestType, username, currency }

theorem UserRequest.decode_agrees (record : UserRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ UserRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserRequest.decode tokens = some record := by
  have distinct : UserRequest.tags.flatten.Nodup := by decide +kernel
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userRequestType := readRequired_part [57, 50, 52] record.userRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [UserRequest.decode, userRequestID, userRequestType, username, currency, some_bind] <;> rfl

theorem UserRequest.taken (record : UserRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 50, 51] record.userRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 50, 52] record.userRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
      (paired_none pairing))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)
  | massQuote (header : Header) (r0 : MassQuote)
  | mMProtectionLimits (header : Header) (r0 : MMProtectionLimits)
  | mMProtectionReset (header : Header) (r0 : MMProtectionReset)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest)
  | quoteCancel (header : Header) (r0 : QuoteCancel)
  | reject (header : Header) (r0 : Reject)
  | requestForPositions (header : Header) (r0 : RequestForPositions)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest)
  | securityListRequest (header : Header) (r0 : SecurityListRequest)
  | securityStatusRequest (header : Header) (r0 : SecurityStatusRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest)
  | userRequest (header : Header) (r0 : UserRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], [86]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .massQuote header r0 => ⟨[51, 53], [105]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .mMProtectionLimits header r0 => ⟨[51, 53], [77, 77]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .mMProtectionReset header r0 => ⟨[51, 53], [77, 90]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], [113]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassStatusRequest header r0 => ⟨[51, 53], [65, 70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteCancel header r0 => ⟨[51, 53], [90]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .requestForPositions header r0 => ⟨[51, 53], [65, 78]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinitionRequest header r0 => ⟨[51, 53], [99]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityListRequest header r0 => ⟨[51, 53], [120]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityStatusRequest header r0 => ⟨[51, 53], [101]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequest header r0 => ⟨[51, 53], [65, 68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userRequest header r0 => ⟨[51, 53], [66, 69]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [53] then
        if known (Header.tags ++ Logout.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logout.decode rest
          pure (.logout header r0)
        else none
      else if token.value = [86] then
        if known (Header.tags ++ MarketDataRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequest.decode rest
          pure (.marketDataRequest header r0)
        else none
      else if token.value = [105] then
        if known (Header.tags ++ MassQuote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MassQuote.decode rest
          pure (.massQuote header r0)
        else none
      else if token.value = [77, 77] then
        if known (Header.tags ++ MMProtectionLimits.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MMProtectionLimits.decode rest
          pure (.mMProtectionLimits header r0)
        else none
      else if token.value = [77, 90] then
        if known (Header.tags ++ MMProtectionReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MMProtectionReset.decode rest
          pure (.mMProtectionReset header r0)
        else none
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
        else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
        else none
      else if token.value = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
        else none
      else if token.value = [65, 70] then
        if known (Header.tags ++ OrderMassStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassStatusRequest.decode rest
          pure (.orderMassStatusRequest header r0)
        else none
      else if token.value = [90] then
        if known (Header.tags ++ QuoteCancel.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteCancel.decode rest
          pure (.quoteCancel header r0)
        else none
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [65, 78] then
        if known (Header.tags ++ RequestForPositions.tags) rest then do
          let header ← Header.decode rest
          let r0 ← RequestForPositions.decode rest
          pure (.requestForPositions header r0)
        else none
      else if token.value = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
        else none
      else if token.value = [99] then
        if known (Header.tags ++ SecurityDefinitionRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinitionRequest.decode rest
          pure (.securityDefinitionRequest header r0)
        else none
      else if token.value = [120] then
        if known (Header.tags ++ SecurityListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityListRequest.decode rest
          pure (.securityListRequest header r0)
        else none
      else if token.value = [101] then
        if known (Header.tags ++ SecurityStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityStatusRequest.decode rest
          pure (.securityStatusRequest header r0)
        else none
      else if token.value = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [49] then
        if known (Header.tags ++ TestRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TestRequest.decode rest
          pure (.testRequest header r0)
        else none
      else if token.value = [65, 68] then
        if known (Header.tags ++ TradeCaptureReportRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequest.decode rest
          pure (.tradeCaptureReportRequest header r0)
        else none
      else if token.value = [66, 69] then
        if known (Header.tags ++ UserRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserRequest.decode rest
          pure (.userRequest header r0)
        else none
      else none
    else none

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decode (Message.tokens (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_massQuote (header : Header) (r0 : MassQuote) :
    Message.decode (Message.tokens (.massQuote header r0)) = some (.massQuote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) rfl rfl (by decide +kernel))
  have c1 := MassQuote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MassQuote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MassQuote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_mMProtectionLimits (header : Header) (r0 : MMProtectionLimits) :
    Message.decode (Message.tokens (.mMProtectionLimits header r0)) = some (.mMProtectionLimits header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionLimits.tags) rfl rfl (by decide +kernel))
  have c1 := MMProtectionLimits.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionLimits.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MMProtectionLimits.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_mMProtectionReset (header : Header) (r0 : MMProtectionReset) :
    Message.decode (Message.tokens (.mMProtectionReset header r0)) = some (.mMProtectionReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionReset.tags) rfl rfl (by decide +kernel))
  have c1 := MMProtectionReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MMProtectionReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MMProtectionReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decode (Message.tokens (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decode (Message.tokens (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteCancel.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteCancel.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_requestForPositions (header : Header) (r0 : RequestForPositions) :
    Message.decode (Message.tokens (.requestForPositions header r0)) = some (.requestForPositions header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (RequestForPositions.tags) rfl rfl (by decide +kernel))
  have c1 := RequestForPositions.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (RequestForPositions.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ RequestForPositions.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decode (Message.tokens (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinitionRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinitionRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinitionRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decode (Message.tokens (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityStatusRequest (header : Header) (r0 : SecurityStatusRequest) :
    Message.decode (Message.tokens (.securityStatusRequest header r0)) = some (.securityStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityStatusRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decode (Message.tokens (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userRequest (header : Header) (r0 : UserRequest) :
    Message.decode (Message.tokens (.userRequest header r0)) = some (.userRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) rfl rfl (by decide +kernel))
  have c1 := UserRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0
  | massQuote header r0 => exact Message.decode_massQuote header r0
  | mMProtectionLimits header r0 => exact Message.decode_mMProtectionLimits header r0
  | mMProtectionReset header r0 => exact Message.decode_mMProtectionReset header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | orderMassStatusRequest header r0 => exact Message.decode_orderMassStatusRequest header r0
  | quoteCancel header r0 => exact Message.decode_quoteCancel header r0
  | reject header r0 => exact Message.decode_reject header r0
  | requestForPositions header r0 => exact Message.decode_requestForPositions header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decode_securityDefinitionRequest header r0
  | securityListRequest header r0 => exact Message.decode_securityListRequest header r0
  | securityStatusRequest header r0 => exact Message.decode_securityStatusRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decode_tradeCaptureReportRequest header r0
  | userRequest header r0 => exact Message.decode_userRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_logout (header : Header) (r0 : Logout) :
    Message.decodeBytes (Message.encode (.logout header r0)) = some (.logout header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [53]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logout.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logout header r0

theorem Message.decodeBytes_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decodeBytes (Message.encode (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [86]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequest header r0

theorem Message.decodeBytes_massQuote (header : Header) (r0 : MassQuote) :
    Message.decodeBytes (Message.encode (.massQuote header r0)) = some (.massQuote header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [105]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MassQuote.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_massQuote header r0

theorem Message.decodeBytes_mMProtectionLimits (header : Header) (r0 : MMProtectionLimits) :
    Message.decodeBytes (Message.encode (.mMProtectionLimits header r0)) = some (.mMProtectionLimits header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [77, 77]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MMProtectionLimits.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_mMProtectionLimits header r0

theorem Message.decodeBytes_mMProtectionReset (header : Header) (r0 : MMProtectionReset) :
    Message.decodeBytes (Message.encode (.mMProtectionReset header r0)) = some (.mMProtectionReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [77, 90]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MMProtectionReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_mMProtectionReset header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [113]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderMassCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

theorem Message.decodeBytes_orderMassStatusRequest (header : Header) (r0 : OrderMassStatusRequest) :
    Message.decodeBytes (Message.encode (.orderMassStatusRequest header r0)) = some (.orderMassStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderMassStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassStatusRequest header r0

theorem Message.decodeBytes_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decodeBytes (Message.encode (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [90]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (QuoteCancel.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteCancel header r0

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_requestForPositions (header : Header) (r0 : RequestForPositions) :
    Message.decodeBytes (Message.encode (.requestForPositions header r0)) = some (.requestForPositions header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 78]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (RequestForPositions.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_requestForPositions header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [50]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ResendRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

theorem Message.decodeBytes_securityDefinitionRequest (header : Header) (r0 : SecurityDefinitionRequest) :
    Message.decodeBytes (Message.encode (.securityDefinitionRequest header r0)) = some (.securityDefinitionRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [99]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinitionRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinitionRequest header r0

theorem Message.decodeBytes_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decodeBytes (Message.encode (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [120]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityListRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityListRequest header r0

theorem Message.decodeBytes_securityStatusRequest (header : Header) (r0 : SecurityStatusRequest) :
    Message.decodeBytes (Message.encode (.securityStatusRequest header r0)) = some (.securityStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [101]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityStatusRequest header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_testRequest (header : Header) (r0 : TestRequest) :
    Message.decodeBytes (Message.encode (.testRequest header r0)) = some (.testRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [49]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TestRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_testRequest header r0

theorem Message.decodeBytes_tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequest header r0)) = some (.tradeCaptureReportRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReportRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequest header r0

theorem Message.decodeBytes_userRequest (header : Header) (r0 : UserRequest) :
    Message.decodeBytes (Message.encode (.userRequest header r0)) = some (.userRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66, 69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0
  | massQuote header r0 => exact Message.decodeBytes_massQuote header r0
  | mMProtectionLimits header r0 => exact Message.decodeBytes_mMProtectionLimits header r0
  | mMProtectionReset header r0 => exact Message.decodeBytes_mMProtectionReset header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | orderMassStatusRequest header r0 => exact Message.decodeBytes_orderMassStatusRequest header r0
  | quoteCancel header r0 => exact Message.decodeBytes_quoteCancel header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | requestForPositions header r0 => exact Message.decodeBytes_requestForPositions header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityDefinitionRequest header r0 => exact Message.decodeBytes_securityDefinitionRequest header r0
  | securityListRequest header r0 => exact Message.decodeBytes_securityListRequest header r0
  | securityStatusRequest header r0 => exact Message.decodeBytes_securityStatusRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decodeBytes_tradeCaptureReportRequest header r0
  | userRequest header r0 => exact Message.decodeBytes_userRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseDeribitOrderentryFixV10Client
