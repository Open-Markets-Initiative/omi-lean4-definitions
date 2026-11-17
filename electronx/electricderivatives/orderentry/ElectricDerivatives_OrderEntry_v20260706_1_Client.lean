import Wire

/-!
# ElectronX Markets Order Entry v20260706.1, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.ElectronxElectricderivativesOrderentryFixV202607061Client

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 48], [57, 49]), ([57, 53], [57, 54]), ([50, 49, 50], [50, 49, 51])]

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  deliverToCompID : Option (Terminated 1)  -- tag 128
  secureData : Option (List UInt8)  -- tag 91
  msgSeqNum : Terminated 1  -- tag 34
  senderSubID : Option (Terminated 1)  -- tag 50
  senderLocationID : Option (Terminated 1)  -- tag 142
  targetSubID : Option (Terminated 1)  -- tag 57
  targetLocationID : Option (Terminated 1)  -- tag 143
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  onBehalfOfLocationID : Option (Terminated 1)  -- tag 144
  deliverToSubID : Option (Terminated 1)  -- tag 129
  deliverToLocationID : Option (Terminated 1)  -- tag 145
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  xmlData : Option (List UInt8)  -- tag 213
  messageEncoding : Option (Terminated 1)  -- tag 347
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369
  applVerID : Option (Terminated 1)  -- tag 1128
  cstmApplVerID : Option (Terminated 1)  -- tag 1129

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.dataOptional [57, 48] [57, 49] record.secureData,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [49, 52, 50] record.senderLocationID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [49, 52, 51] record.targetLocationID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 52, 52] record.onBehalfOfLocationID,
   Part.optional [49, 50, 57] record.deliverToSubID,
   Part.optional [49, 52, 53] record.deliverToLocationID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.dataOptional [50, 49, 50] [50, 49, 51] record.xmlData,
   Part.optional [51, 52, 55] record.messageEncoding,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed,
   Part.optional [49, 49, 50, 56] record.applVerID,
   Part.optional [49, 49, 50, 57] record.cstmApplVerID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[49, 49, 53]], [[49, 50, 56]], [[57, 48], [57, 49]], [[51, 52]], [[53, 48]], [[49, 52, 50]], [[53, 55]], [[49, 52, 51]], [[49, 49, 54]], [[49, 52, 52]], [[49, 50, 57]], [[49, 52, 53]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[50, 49, 50], [50, 49, 51]], [[51, 52, 55]], [[51, 54, 57]], [[49, 49, 50, 56]], [[49, 49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let secureData ← readDataOptional [57, 48] [57, 49] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let senderLocationID ← readOptional [49, 52, 50] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let targetLocationID ← readOptional [49, 52, 51] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let onBehalfOfLocationID ← readOptional [49, 52, 52] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  let deliverToLocationID ← readOptional [49, 52, 53] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let xmlData ← readDataOptional [50, 49, 50] [50, 49, 51] tokens
  let messageEncoding ← readOptional [51, 52, 55] tokens
  let lastMsgSeqNumProcessed ← readOptional [51, 54, 57] tokens
  let applVerID ← readOptional [49, 49, 50, 56] tokens
  let cstmApplVerID ← readOptional [49, 49, 50, 57] tokens
  pure { senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, applVerID, cstmApplVerID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have secureData := readDataOptional_part [57, 48] [57, 49] record.secureData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have senderLocationID := readOptional_part [49, 52, 50] record.senderLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have targetLocationID := readOptional_part [49, 52, 51] record.targetLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have onBehalfOfLocationID := readOptional_part [49, 52, 52] record.onBehalfOfLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have deliverToLocationID := readOptional_part [49, 52, 53] record.deliverToLocationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have xmlData := readDataOptional_part [50, 49, 50] [50, 49, 51] record.xmlData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have messageEncoding := readOptional_part [51, 52, 55] record.messageEncoding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have lastMsgSeqNumProcessed := readOptional_part [51, 54, 57] record.lastMsgSeqNumProcessed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have applVerID := readOptional_part [49, 49, 50, 56] record.applVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have cstmApplVerID := readOptional_part [49, 49, 50, 57] record.cstmApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, applVerID, cstmApplVerID, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 53] record.onBehalfOfCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 50, 56] record.deliverToCompID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_dataOptional pairing [57, 48] [57, 49] record.secureData (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 52, 50] record.senderLocationID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 52, 51] record.targetLocationID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 54] record.onBehalfOfSubID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 52, 52] record.onBehalfOfLocationID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 50, 57] record.deliverToSubID (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 52, 53] record.deliverToLocationID (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_dataOptional pairing [50, 49, 50] [50, 49, 51] record.xmlData (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [51, 52, 55] record.messageEncoding (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [51, 54, 57] record.lastMsgSeqNumProcessed (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 56] record.applVerID (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 57] record.cstmApplVerID (by decide) (by decide))
                         (paired_none pairing)))))))))))))))))))))))

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

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  rawData : Option (List UInt8)  -- tag 96
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  username : Option (Terminated 1)  -- tag 553
  password : Option (Terminated 1)  -- tag 554
  defaultApplVerID : Terminated 1  -- tag 1137

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.dataOptional [57, 53] [57, 54] record.rawData,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [53, 53, 51] record.username,
   Part.optional [53, 53, 52] record.password,
   Part.required [49, 49, 51, 55] record.defaultApplVerID]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[57, 53], [57, 54]], [[49, 52, 49]], [[53, 53, 51]], [[53, 53, 52]], [[49, 49, 51, 55]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let username ← readOptional [53, 53, 51] tokens
  let password ← readOptional [53, 53, 52] tokens
  let defaultApplVerID ← readRequired [49, 49, 51, 55] tokens
  pure { encryptMethod, heartBtInt, rawData, resetSeqNumFlag, username, password, defaultApplVerID }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rawData := readDataOptional_part [57, 53] [57, 54] record.rawData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have username := readOptional_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have defaultApplVerID := readRequired_part [49, 49, 51, 55] record.defaultApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, rawData, resetSeqNumFlag, username, password, defaultApplVerID, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53, 51] record.username (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52] record.password (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [49, 49, 51, 55] record.defaultApplVerID (by decide) (by decide))
         (paired_none pairing)))))))

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

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

structure NewOrderSingle where
  account : Terminated 1  -- tag 1
  orderCapacity : Option (Terminated 1)  -- tag 528
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  orderQty : Terminated 1  -- tag 38
  cashOrderQty : Option (Terminated 1)  -- tag 152
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  product : Option (Terminated 1)  -- tag 460
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  maturityDate : Option (Terminated 1)  -- tag 541
  contractMultiplier : Option (Terminated 1)  -- tag 231
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  timeInForce : Terminated 1  -- tag 59
  minQty : Option (Terminated 1)  -- tag 110
  expireTime : Option (Terminated 1)  -- tag 126
  commission : Option (Terminated 1)  -- tag 12
  commType : Option (Terminated 1)  -- tag 13
  conditionTriggerMethod : Option (Terminated 1)  -- tag 6127
  text : Option (Terminated 1)  -- tag 58
  selfMatchPreventionID : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 8000
  custOrderCapacity : Terminated 1  -- tag 582
  designation : Option (Terminated 1)  -- tag 494
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  manualOrderIndicator : Terminated 1  -- tag 1028

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49] record.account,
   Part.optional [53, 50, 56] record.orderCapacity,
   Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 53, 50] record.cashOrderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 54, 48] record.product,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.required [53, 57] record.timeInForce,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [49, 50] record.commission,
   Part.optional [49, 51] record.commType,
   Part.optional [54, 49, 50, 55] record.conditionTriggerMethod,
   Part.optional [53, 56] record.text,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionID,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionInstruction,
   Part.required [53, 56, 50] record.custOrderCapacity,
   Part.optional [52, 57, 52] record.designation,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49]], [[53, 50, 56]], [[49, 49]], [[49, 56]], [[51, 56]], [[49, 53, 50]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[52, 56]], [[50, 50]], [[52, 54, 48]], [[49, 54, 55]], [[55, 54, 50]], [[53, 52, 49]], [[50, 51, 49]], [[57, 54, 57]], [[53, 57]], [[49, 49, 48]], [[49, 50, 54]], [[49, 50]], [[49, 51]], [[54, 49, 50, 55]], [[53, 56]], [[55, 57, 50, 56]], [[56, 48, 48, 48]], [[53, 56, 50]], [[52, 57, 52]], [[53, 56, 51]], [[49, 48, 50, 56]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let account ← readRequired [49] tokens
  let orderCapacity ← readOptional [53, 50, 56] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let orderQty ← readRequired [51, 56] tokens
  let cashOrderQty ← readOptional [49, 53, 50] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let product ← readOptional [52, 54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let commission ← readOptional [49, 50] tokens
  let commType ← readOptional [49, 51] tokens
  let conditionTriggerMethod ← readOptional [54, 49, 50, 55] tokens
  let text ← readOptional [53, 56] tokens
  let selfMatchPreventionID ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionInstruction ← readOptional [56, 48, 48, 48] tokens
  let custOrderCapacity ← readRequired [53, 56, 50] tokens
  let designation ← readOptional [52, 57, 52] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  pure { account, orderCapacity, clOrdID, execInst, orderQty, cashOrderQty, ordType, price, side, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, timeInForce, minQty, expireTime, commission, commType, conditionTriggerMethod, text, selfMatchPreventionID, selfMatchPreventionInstruction, custOrderCapacity, designation, clOrdLinkID, manualOrderIndicator }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderCapacity := readOptional_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cashOrderQty := readOptional_part [49, 53, 50] record.cashOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have product := readOptional_part [52, 54, 48] record.product tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have commission := readOptional_part [49, 50] record.commission tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have commType := readOptional_part [49, 51] record.commType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have conditionTriggerMethod := readOptional_part [54, 49, 50, 55] record.conditionTriggerMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have selfMatchPreventionID := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have custOrderCapacity := readRequired_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have designation := readOptional_part [52, 57, 52] record.designation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  simp only [NewOrderSingle.decode, account, orderCapacity, clOrdID, execInst, orderQty, cashOrderQty, ordType, price, side, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, timeInForce, minQty, expireTime, commission, commType, conditionTriggerMethod, text, selfMatchPreventionID, selfMatchPreventionInstruction, custOrderCapacity, designation, clOrdLinkID, manualOrderIndicator, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50] record.cashOrderQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 54, 48] record.product (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 50] record.commission (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 51] record.commType (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [54, 49, 50, 55] record.conditionTriggerMethod (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionID (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionInstruction (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_required pairing [53, 56, 50] record.custOrderCapacity (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [52, 57, 52] record.designation (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 56, 51] record.clOrdLinkID (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
                                 (paired_none pairing)))))))))))))))))))))))))))))))

structure OrderCancelReplaceRequest where
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Terminated 1  -- tag 11
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  origClOrdID : Terminated 1  -- tag 41
  account : Terminated 1  -- tag 1
  accountType : Option (Terminated 1)  -- tag 581
  custOrderCapacity : Option (Terminated 1)  -- tag 582
  execInst : Option (Terminated 1)  -- tag 18
  minQty : Option (Terminated 1)  -- tag 110
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  product : Option (Terminated 1)  -- tag 460
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  maturityDate : Option (Terminated 1)  -- tag 541
  contractMultiplier : Option (Terminated 1)  -- tag 231
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  side : Option (Terminated 1)  -- tag 54
  transactTime : Option (Terminated 1)  -- tag 60
  orderQty : Option (Terminated 1)  -- tag 38
  cashOrderQty : Option (Terminated 1)  -- tag 152
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  timeInForce : Option (Terminated 1)  -- tag 59
  expireTime : Option (Terminated 1)  -- tag 126
  text : Option (Terminated 1)  -- tag 58

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.optional [51, 55] record.orderID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.required [52, 49] record.origClOrdID,
   Part.required [49] record.account,
   Part.optional [53, 56, 49] record.accountType,
   Part.optional [53, 56, 50] record.custOrderCapacity,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 54, 48] record.product,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.optional [53, 52] record.side,
   Part.optional [54, 48] record.transactTime,
   Part.optional [51, 56] record.orderQty,
   Part.optional [49, 53, 50] record.cashOrderQty,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [53, 56] record.text]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[51, 55]], [[49, 49]], [[53, 56, 51]], [[52, 49]], [[49]], [[53, 56, 49]], [[53, 56, 50]], [[49, 56]], [[49, 49, 48]], [[53, 53]], [[52, 56]], [[50, 50]], [[52, 54, 48]], [[49, 54, 55]], [[55, 54, 50]], [[53, 52, 49]], [[50, 51, 49]], [[57, 54, 57]], [[53, 52]], [[54, 48]], [[51, 56]], [[49, 53, 50]], [[52, 48]], [[52, 52]], [[53, 57]], [[49, 50, 54]], [[53, 56]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let account ← readRequired [49] tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let custOrderCapacity ← readOptional [53, 56, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let product ← readOptional [52, 54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let side ← readOptional [53, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let orderQty ← readOptional [51, 56] tokens
  let cashOrderQty ← readOptional [49, 53, 50] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let text ← readOptional [53, 56] tokens
  pure { orderID, clOrdID, clOrdLinkID, origClOrdID, account, accountType, custOrderCapacity, execInst, minQty, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, side, transactTime, orderQty, cashOrderQty, ordType, price, timeInForce, expireTime, text }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have custOrderCapacity := readOptional_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have product := readOptional_part [52, 54, 48] record.product tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have orderQty := readOptional_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have cashOrderQty := readOptional_part [49, 53, 50] record.cashOrderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, orderID, clOrdID, clOrdLinkID, origClOrdID, account, accountType, custOrderCapacity, execInst, minQty, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, side, transactTime, orderQty, cashOrderQty, ordType, price, timeInForce, expireTime, text, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56, 51] record.clOrdLinkID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 56, 49] record.accountType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 56, 50] record.custOrderCapacity (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 54, 48] record.product (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [51, 56] record.orderQty (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50] record.cashOrderQty (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                             (paired_none pairing)))))))))))))))))))))))))))

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  clOrdLinkID : Option (Terminated 1)  -- tag 583
  account : Option (Terminated 1)  -- tag 1
  accountType : Option (Terminated 1)  -- tag 581
  origClOrdID : Terminated 1  -- tag 41
  orderID : Option (Terminated 1)  -- tag 37
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  product : Option (Terminated 1)  -- tag 460
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  maturityDate : Option (Terminated 1)  -- tag 541
  contractMultiplier : Option (Terminated 1)  -- tag 231
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  side : Option (Terminated 1)  -- tag 54
  transactTime : Option (Terminated 1)  -- tag 60
  text : Option (Terminated 1)  -- tag 58

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [53, 56, 51] record.clOrdLinkID,
   Part.optional [49] record.account,
   Part.optional [53, 56, 49] record.accountType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 54, 48] record.product,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.optional [53, 52] record.side,
   Part.optional [54, 48] record.transactTime,
   Part.optional [53, 56] record.text]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 56, 51]], [[49]], [[53, 56, 49]], [[52, 49]], [[51, 55]], [[53, 53]], [[52, 56]], [[50, 50]], [[52, 54, 48]], [[49, 54, 55]], [[55, 54, 50]], [[53, 52, 49]], [[50, 51, 49]], [[57, 54, 57]], [[53, 52]], [[54, 48]], [[53, 56]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  let account ← readOptional [49] tokens
  let accountType ← readOptional [53, 56, 49] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let product ← readOptional [52, 54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let side ← readOptional [53, 52] tokens
  let transactTime ← readOptional [54, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { clOrdID, clOrdLinkID, account, accountType, origClOrdID, orderID, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, side, transactTime, text }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have accountType := readOptional_part [53, 56, 49] record.accountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have product := readOptional_part [52, 54, 48] record.product tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, clOrdLinkID, account, accountType, origClOrdID, orderID, symbol, securityID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, side, transactTime, text, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56, 51] record.clOrdLinkID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56, 49] record.accountType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [52, 54, 48] record.product (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                    (paired_none pairing))))))))))))))))))

structure OrderMassCancelRequest where
  account : Option (Terminated 1)  -- tag 1
  text : Option (Terminated 1)  -- tag 58
  clOrdID : Terminated 1  -- tag 11
  securityIDSource : Option (Terminated 1)  -- tag 22
  product : Option (Terminated 1)  -- tag 460
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  maturityDate : Option (Terminated 1)  -- tag 541
  contractMultiplier : Option (Terminated 1)  -- tag 231
  minPriceIncrement : Option (Terminated 1)  -- tag 969
  securityID : Option (Terminated 1)  -- tag 48
  symbol : Option (Terminated 1)  -- tag 55
  massCancelRequestType : Terminated 1  -- tag 530
  clOrdLinkID : Option (Terminated 1)  -- tag 583

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.optional [49] record.account,
   Part.optional [53, 56] record.text,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 50] record.securityIDSource,
   Part.optional [52, 54, 48] record.product,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [53, 52, 49] record.maturityDate,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 54, 57] record.minPriceIncrement,
   Part.optional [52, 56] record.securityID,
   Part.optional [53, 53] record.symbol,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [53, 56, 51] record.clOrdLinkID]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49]], [[53, 56]], [[49, 49]], [[50, 50]], [[52, 54, 48]], [[49, 54, 55]], [[55, 54, 50]], [[53, 52, 49]], [[50, 51, 49]], [[57, 54, 57]], [[52, 56]], [[53, 53]], [[53, 51, 48]], [[53, 56, 51]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let account ← readOptional [49] tokens
  let text ← readOptional [53, 56] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let product ← readOptional [52, 54, 48] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let maturityDate ← readOptional [53, 52, 49] tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let minPriceIncrement ← readOptional [57, 54, 57] tokens
  let securityID ← readOptional [52, 56] tokens
  let symbol ← readOptional [53, 53] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let clOrdLinkID ← readOptional [53, 56, 51] tokens
  pure { account, text, clOrdID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, securityID, symbol, massCancelRequestType, clOrdLinkID }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have product := readOptional_part [52, 54, 48] record.product tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityDate := readOptional_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have minPriceIncrement := readOptional_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have clOrdLinkID := readOptional_part [53, 56, 51] record.clOrdLinkID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, account, text, clOrdID, securityIDSource, product, securityType, securitySubType, maturityDate, contractMultiplier, minPriceIncrement, securityID, symbol, massCancelRequestType, clOrdLinkID, some_bind] <;> rfl

theorem OrderMassCancelRequest.taken (record : OrderMassCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 54, 48] record.product (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.massCancelRequestType (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 56, 51] record.clOrdLinkID (by decide) (by decide))
                (paired_none pairing))))))))))))))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  pure { refSeqNum, text, refTagID, refMsgType, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
       (paired_none pairing)))))

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

theorem SequenceReset.taken (record : SequenceReset) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 50, 51] record.gapFillFlag (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 54] record.newSeqNo (by decide) (by decide))
    (paired_none pairing))

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

theorem TestRequest.taken (record : TestRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], [113]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [51] then
        if known (Header.tags ++ Reject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Reject.decode rest
          pure (.reject header r0)
        else none
      else if token.value = [50] then
        if known (Header.tags ++ ResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ResendRequest.decode rest
          pure (.resendRequest header r0)
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

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

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

theorem Message.decodeBytes_reject (header : Header) (r0 : Reject) :
    Message.decodeBytes (Message.encode (.reject header r0)) = some (.reject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Reject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_reject header r0

theorem Message.decodeBytes_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decodeBytes (Message.encode (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [50]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ResendRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_resendRequest header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIXT.1.1 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 84, 46, 49, 46, 49, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.ElectronxElectricderivativesOrderentryFixV202607061Client
