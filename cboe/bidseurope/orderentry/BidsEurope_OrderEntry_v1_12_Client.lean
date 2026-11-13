import Wire

/-!
# Chicago Board Options Exchange Order Entry v1.12, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBidseuropeOrderentryFixV112Client

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

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Option (Terminated 1)  -- tag 447
  partyRole : Option (Terminated 1)  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.optional [52, 52, 55] record.partyIDSource,
   Part.optional [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readOptional [52, 52, 55] tokens
  let partyRole ← readOptional [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readOptional_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readOptional_part [52, 53, 50] record.partyRole tokens
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

structure NewOrderSingle where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Option (Terminated 1)  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  iOIid : Option (Terminated 1)  -- tag 23
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  securityExchange : Option (Terminated 1)  -- tag 207
  pegDifference : Option (Terminated 1)  -- tag 211
  clearingFirm : Option (Terminated 1)  -- tag 439
  noPartyIDs : List NoPartyIDs  -- tag 453
  orderCapacity : Option (Terminated 1)  -- tag 528
  bookingType : Option (Terminated 1)  -- tag 775
  bIDSType : Terminated 1  -- tag 8002
  bIDSInvite : Option (Terminated 1)  -- tag 8003
  bIDSFilterLevel : Option (Terminated 1)  -- tag 8007
  bIDSTradePriority : Option (Terminated 1)  -- tag 8008
  bIDSPriceProtection : Option (Terminated 1)  -- tag 8017
  bIDSFirmUpMode : Option (Terminated 1)  -- tag 8065
  partyIDOrderOriginationFirm : Option (Terminated 1)  -- tag 20013

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.optional [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.optional [50, 51] record.iOIid,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 55, 53] record.bookingType,
   Part.required [56, 48, 48, 50] record.bIDSType,
   Part.optional [56, 48, 48, 51] record.bIDSInvite,
   Part.optional [56, 48, 48, 55] record.bIDSFilterLevel,
   Part.optional [56, 48, 48, 56] record.bIDSTradePriority,
   Part.optional [56, 48, 49, 55] record.bIDSPriceProtection,
   Part.optional [56, 48, 54, 53] record.bIDSFirmUpMode,
   Part.optional [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[50, 51]], [[51, 56]], [[52, 48]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[49, 49, 48]], [[49, 50, 54]], [[50, 48, 55]], [[50, 49, 49]], [[52, 51, 57]], [52, 53, 51] :: NoPartyIDs.members, [[53, 50, 56]], [[55, 55, 53]], [[56, 48, 48, 50]], [[56, 48, 48, 51]], [[56, 48, 48, 55]], [[56, 48, 48, 56]], [[56, 48, 49, 55]], [[56, 48, 54, 53]], [[50, 48, 48, 49, 51]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readOptional [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let iOIid ← readOptional [50, 51] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  let bIDSType ← readRequired [56, 48, 48, 50] tokens
  let bIDSInvite ← readOptional [56, 48, 48, 51] tokens
  let bIDSFilterLevel ← readOptional [56, 48, 48, 55] tokens
  let bIDSTradePriority ← readOptional [56, 48, 48, 56] tokens
  let bIDSPriceProtection ← readOptional [56, 48, 49, 55] tokens
  let bIDSFirmUpMode ← readOptional [56, 48, 54, 53] tokens
  let partyIDOrderOriginationFirm ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, currency, execInst, handlInst, iDSource, iOIid, orderQty, ordType, price, securityID, side, symbol, text, timeInForce, transactTime, execBroker, minQty, expireTime, securityExchange, pegDifference, clearingFirm, noPartyIDs, orderCapacity, bookingType, bIDSType, bIDSInvite, bIDSFilterLevel, bIDSTradePriority, bIDSPriceProtection, bIDSFirmUpMode, partyIDOrderOriginationFirm }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have iOIid := readOptional_part [50, 51] record.iOIid tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have bIDSType := readRequired_part [56, 48, 48, 50] record.bIDSType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have bIDSInvite := readOptional_part [56, 48, 48, 51] record.bIDSInvite tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have bIDSFilterLevel := readOptional_part [56, 48, 48, 55] record.bIDSFilterLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have bIDSTradePriority := readOptional_part [56, 48, 48, 56] record.bIDSTradePriority tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have bIDSPriceProtection := readOptional_part [56, 48, 49, 55] record.bIDSPriceProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have bIDSFirmUpMode := readOptional_part [56, 48, 54, 53] record.bIDSFirmUpMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have partyIDOrderOriginationFirm := readOptional_part [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, clOrdID, currency, execInst, handlInst, iDSource, iOIid, orderQty, ordType, price, securityID, side, symbol, text, timeInForce, transactTime, execBroker, minQty, expireTime, securityExchange, pegDifference, clearingFirm, noPartyIDs, orderCapacity, bookingType, bIDSType, bIDSInvite, bIDSFilterLevel, bIDSTradePriority, bIDSPriceProtection, bIDSFirmUpMode, partyIDOrderOriginationFirm, some_bind] <;> rfl

structure CancelAndReplaceRequestIOIFirmupModificationRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Option (Terminated 1)  -- tag 21
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  securityExchange : Option (Terminated 1)  -- tag 207
  pegDifference : Option (Terminated 1)  -- tag 211
  clearingFirm : Option (Terminated 1)  -- tag 439
  noPartyIDs : List NoPartyIDs  -- tag 453
  orderCapacity : Option (Terminated 1)  -- tag 528
  bookingType : Option (Terminated 1)  -- tag 775
  bIDSType : Terminated 1  -- tag 8002
  bIDSInvite : Option (Terminated 1)  -- tag 8003
  bIDSFilterLevel : Option (Terminated 1)  -- tag 8007
  bIDSTradePriority : Option (Terminated 1)  -- tag 8008
  bIDSPriceProtection : Option (Terminated 1)  -- tag 8017
  bIDSFirmUpMode : Option (Terminated 1)  -- tag 8065
  partyIDOrderOriginationFirm : Option (Terminated 1)  -- tag 20013

def CancelAndReplaceRequestIOIFirmupModificationRequest.parts (record : CancelAndReplaceRequestIOIFirmupModificationRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [49, 56] record.execInst,
   Part.optional [50, 49] record.handlInst,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.optional [55, 55, 53] record.bookingType,
   Part.required [56, 48, 48, 50] record.bIDSType,
   Part.optional [56, 48, 48, 51] record.bIDSInvite,
   Part.optional [56, 48, 48, 55] record.bIDSFilterLevel,
   Part.optional [56, 48, 48, 56] record.bIDSTradePriority,
   Part.optional [56, 48, 49, 55] record.bIDSPriceProtection,
   Part.optional [56, 48, 54, 53] record.bIDSFirmUpMode,
   Part.optional [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm]

def CancelAndReplaceRequestIOIFirmupModificationRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[49, 56]], [[50, 49]], [[50, 50]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[53, 57]], [[54, 48]], [[55, 54]], [[49, 49, 48]], [[49, 50, 54]], [[50, 48, 55]], [[50, 49, 49]], [[52, 51, 57]], [52, 53, 51] :: NoPartyIDs.members, [[53, 50, 56]], [[55, 55, 53]], [[56, 48, 48, 50]], [[56, 48, 48, 51]], [[56, 48, 48, 55]], [[56, 48, 48, 56]], [[56, 48, 49, 55]], [[56, 48, 54, 53]], [[50, 48, 48, 49, 51]]]

theorem CancelAndReplaceRequestIOIFirmupModificationRequest.shape (record : CancelAndReplaceRequestIOIFirmupModificationRequest) : record.parts.map Part.tags = CancelAndReplaceRequestIOIFirmupModificationRequest.tags := rfl

def CancelAndReplaceRequestIOIFirmupModificationRequest.decode (tokens : List Token) : Option CancelAndReplaceRequestIOIFirmupModificationRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readOptional [50, 49] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  let bIDSType ← readRequired [56, 48, 48, 50] tokens
  let bIDSInvite ← readOptional [56, 48, 48, 51] tokens
  let bIDSFilterLevel ← readOptional [56, 48, 48, 55] tokens
  let bIDSTradePriority ← readOptional [56, 48, 48, 56] tokens
  let bIDSPriceProtection ← readOptional [56, 48, 49, 55] tokens
  let bIDSFirmUpMode ← readOptional [56, 48, 54, 53] tokens
  let partyIDOrderOriginationFirm ← readOptional [50, 48, 48, 49, 51] tokens
  pure { account, clOrdID, currency, execInst, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, execBroker, minQty, expireTime, securityExchange, pegDifference, clearingFirm, noPartyIDs, orderCapacity, bookingType, bIDSType, bIDSInvite, bIDSFilterLevel, bIDSTradePriority, bIDSPriceProtection, bIDSFirmUpMode, partyIDOrderOriginationFirm }

theorem CancelAndReplaceRequestIOIFirmupModificationRequest.decode_agrees (record : CancelAndReplaceRequestIOIFirmupModificationRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ CancelAndReplaceRequestIOIFirmupModificationRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CancelAndReplaceRequestIOIFirmupModificationRequest.decode tokens = some record := by
  have distinct : CancelAndReplaceRequestIOIFirmupModificationRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have bIDSType := readRequired_part [56, 48, 48, 50] record.bIDSType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have bIDSInvite := readOptional_part [56, 48, 48, 51] record.bIDSInvite tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have bIDSFilterLevel := readOptional_part [56, 48, 48, 55] record.bIDSFilterLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have bIDSTradePriority := readOptional_part [56, 48, 48, 56] record.bIDSTradePriority tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have bIDSPriceProtection := readOptional_part [56, 48, 49, 55] record.bIDSPriceProtection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have bIDSFirmUpMode := readOptional_part [56, 48, 54, 53] record.bIDSFirmUpMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have partyIDOrderOriginationFirm := readOptional_part [50, 48, 48, 49, 51] record.partyIDOrderOriginationFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  simp only [CancelAndReplaceRequestIOIFirmupModificationRequest.decode, account, clOrdID, currency, execInst, handlInst, iDSource, orderID, orderQty, ordType, origClOrdID, price, securityID, side, symbol, text, timeInForce, transactTime, execBroker, minQty, expireTime, securityExchange, pegDifference, clearingFirm, noPartyIDs, orderCapacity, bookingType, bIDSType, bIDSInvite, bIDSFilterLevel, bIDSTradePriority, bIDSPriceProtection, bIDSFirmUpMode, partyIDOrderOriginationFirm, some_bind] <;> rfl

structure OrderCancelRequest where
  account : Option (Terminated 1)  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  iDSource : Option (Terminated 1)  -- tag 22
  orderID : Option (Terminated 1)  -- tag 37
  orderQty : Option (Terminated 1)  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  securityID : Option (Terminated 1)  -- tag 48
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  text : Option (Terminated 1)  -- tag 58
  transactTime : Terminated 1  -- tag 60
  execBroker : Option (Terminated 1)  -- tag 76
  securityExchange : Option (Terminated 1)  -- tag 207
  clearingFirm : Option (Terminated 1)  -- tag 439
  bookingType : Option (Terminated 1)  -- tag 775

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.optional [50, 50] record.iDSource,
   Part.optional [51, 55] record.orderID,
   Part.optional [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 56] record.securityID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 56] record.text,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 54] record.execBroker,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 55, 53] record.bookingType]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49]], [[49, 53]], [[50, 50]], [[51, 55]], [[51, 56]], [[52, 49]], [[52, 56]], [[53, 52]], [[53, 53]], [[53, 56]], [[54, 48]], [[55, 54]], [[50, 48, 55]], [[52, 51, 57]], [[55, 55, 53]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let account ← readOptional [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let iDSource ← readOptional [50, 50] tokens
  let orderID ← readOptional [51, 55] tokens
  let orderQty ← readOptional [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let securityID ← readOptional [52, 56] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let text ← readOptional [53, 56] tokens
  let transactTime ← readRequired [54, 48] tokens
  let execBroker ← readOptional [55, 54] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let bookingType ← readOptional [55, 55, 53] tokens
  pure { account, clOrdID, currency, iDSource, orderID, orderQty, origClOrdID, securityID, side, symbol, text, transactTime, execBroker, securityExchange, clearingFirm, bookingType }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have bookingType := readOptional_part [55, 55, 53] record.bookingType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, account, clOrdID, currency, iDSource, orderID, orderQty, origClOrdID, securityID, side, symbol, text, transactTime, execBroker, securityExchange, clearingFirm, bookingType, some_bind] <;> rfl

inductive Message where
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | cancelAndReplaceRequestIOIFirmupModificationRequest (header : Header) (r0 : CancelAndReplaceRequestIOIFirmupModificationRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)

def Message.tokens : Message → List Token
  | .newOrderSingle header r0 => ⟨[51, 53], ⟨[68], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .cancelAndReplaceRequestIOIFirmupModificationRequest header r0 => ⟨[51, 53], ⟨[71], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

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
        if known (Header.tags ++ CancelAndReplaceRequestIOIFirmupModificationRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← CancelAndReplaceRequestIOIFirmupModificationRequest.decode rest
          pure (.cancelAndReplaceRequestIOIFirmupModificationRequest header r0)
        else none
      else if token.value.val = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
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

theorem Message.decode_cancelAndReplaceRequestIOIFirmupModificationRequest (header : Header) (r0 : CancelAndReplaceRequestIOIFirmupModificationRequest) :
    Message.decode (Message.tokens (.cancelAndReplaceRequestIOIFirmupModificationRequest header r0)) = some (.cancelAndReplaceRequestIOIFirmupModificationRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (CancelAndReplaceRequestIOIFirmupModificationRequest.tags) rfl rfl (by decide +kernel))
  have c1 := CancelAndReplaceRequestIOIFirmupModificationRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (CancelAndReplaceRequestIOIFirmupModificationRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ CancelAndReplaceRequestIOIFirmupModificationRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | cancelAndReplaceRequestIOIFirmupModificationRequest header r0 => exact Message.decode_cancelAndReplaceRequestIOIFirmupModificationRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0

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

theorem Message.decodeBytes_cancelAndReplaceRequestIOIFirmupModificationRequest (header : Header) (r0 : CancelAndReplaceRequestIOIFirmupModificationRequest) :
    Message.decodeBytes (Message.encode (.cancelAndReplaceRequestIOIFirmupModificationRequest header r0)) = some (.cancelAndReplaceRequestIOIFirmupModificationRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[71], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ CancelAndReplaceRequestIOIFirmupModificationRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_cancelAndReplaceRequestIOIFirmupModificationRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | cancelAndReplaceRequestIOIFirmupModificationRequest header r0 => exact Message.decodeBytes_cancelAndReplaceRequestIOIFirmupModificationRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeBidseuropeOrderentryFixV112Client
