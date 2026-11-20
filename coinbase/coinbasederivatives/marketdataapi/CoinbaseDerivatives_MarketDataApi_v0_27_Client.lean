import Wire

/-!
# Coinbase  v0.27, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

Note: SignatureLength and Signature stand in the trailer ahead of CheckSum: read by tag wherever they stand, as every field of a body is, and written after the header's other fields.

License: MIT No Attribution
-/

namespace Omi.CoinbaseCoinbasederivativesMarketdataapiFixV027Client

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 48], [57, 49]), ([57, 51], [56, 57]), ([57, 53], [57, 54]), ([50, 49, 50], [50, 49, 51]), ([51, 53, 52], [51, 53, 53])]

structure NoHops where
  hopCompID : Terminated 1  -- tag 628
  hopSendingTime : Option (Terminated 1)  -- tag 629
  hopRefID : Option (Terminated 1)  -- tag 630

def NoHops.parts (record : NoHops) : List Part :=
  [Part.required [54, 50, 56] record.hopCompID,
   Part.optional [54, 50, 57] record.hopSendingTime,
   Part.optional [54, 51, 48] record.hopRefID]

def NoHops.tags : List (List (List UInt8)) :=
  [[[54, 50, 56]], [[54, 50, 57]], [[54, 51, 48]]]

theorem NoHops.shape (record : NoHops) : record.parts.map Part.tags = NoHops.tags := rfl

def NoHops.decode (tokens : List Token) : Option NoHops := do
  let hopCompID ← readRequired [54, 50, 56] tokens
  let hopSendingTime ← readOptional [54, 50, 57] tokens
  let hopRefID ← readOptional [54, 51, 48] tokens
  pure { hopCompID, hopSendingTime, hopRefID }

theorem NoHops.decode_agrees (record : NoHops) (tokens : List Token)
    (agrees : ∀ tags ∈ NoHops.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoHops.decode tokens = some record := by
  have distinct : NoHops.tags.flatten.Nodup := by decide +kernel
  have hopCompID := readRequired_part [54, 50, 56] record.hopCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have hopSendingTime := readOptional_part [54, 50, 57] record.hopSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have hopRefID := readOptional_part [54, 51, 48] record.hopRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoHops.decode, hopCompID, hopSendingTime, hopRefID, some_bind] <;> rfl

theorem NoHops.taken (record : NoHops) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 50, 56] record.hopCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 50, 57] record.hopSendingTime (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 51, 48] record.hopRefID (by decide) (by decide))
     (paired_none pairing)))

def NoHops.members : List (List UInt8) := NoHops.tags.flatten

def NoHops.encode (entry : NoHops) : List Token := encodeParts entry.parts

theorem NoHops.decode_encode (entry : NoHops) : NoHops.decode entry.encode = some entry :=
  NoHops.decode_agrees entry _ (fun _ _ => rfl)

theorem NoHops.within (entry : NoHops) : ∀ token ∈ entry.encode, token.tag ∈ NoHops.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoHops.shape] at this

theorem NoHops.led (entry : NoHops) : Lead [54, 50, 56] entry.encode :=
  lead_parts [54, 50, 56] entry.hopCompID _ NoHops.tags.tail rfl (by decide +kernel)

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
  messageEncoding : Option (Terminated 1)  -- tag 347
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  xmlData : Option (List UInt8)  -- tag 213
  noHops : List NoHops  -- tag 627
  signature : Option (List UInt8)  -- tag 89

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
   Part.optional [51, 52, 55] record.messageEncoding,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.dataOptional [50, 49, 50] [50, 49, 51] record.xmlData,
   Part.group [54, 50, 55] NoHops.members NoHops.encode NoHops.within record.noHops,
   Part.dataOptional [57, 51] [56, 57] record.signature]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[49, 49, 53]], [[49, 50, 56]], [[57, 48], [57, 49]], [[51, 52]], [[53, 48]], [[49, 52, 50]], [[53, 55]], [[49, 52, 51]], [[49, 49, 54]], [[49, 52, 52]], [[49, 50, 57]], [[49, 52, 53]], [[52, 51]], [[57, 55]], [[51, 52, 55]], [[51, 54, 57]], [[53, 50]], [[49, 50, 50]], [[50, 49, 50], [50, 49, 51]], [54, 50, 55] :: NoHops.members, [[57, 51], [56, 57]]]

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
  let messageEncoding ← readOptional [51, 52, 55] tokens
  let lastMsgSeqNumProcessed ← readOptional [51, 54, 57] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let xmlData ← readDataOptional [50, 49, 50] [50, 49, 51] tokens
  let noHops ← readGroup [54, 50, 55] [54, 50, 56] NoHops.members NoHops.decode tokens
  let signature ← readDataOptional [57, 51] [56, 57] tokens
  pure { senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, messageEncoding, lastMsgSeqNumProcessed, sendingTime, origSendingTime, xmlData, noHops, signature }

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
  have messageEncoding := readOptional_part [51, 52, 55] record.messageEncoding tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have lastMsgSeqNumProcessed := readOptional_part [51, 54, 57] record.lastMsgSeqNumProcessed tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have xmlData := readDataOptional_part [50, 49, 50] [50, 49, 51] record.xmlData tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have noHops := readGroup_part [54, 50, 55] [54, 50, 56] NoHops.members NoHops.encode NoHops.within NoHops.decode NoHops.decode_encode NoHops.led record.noHops tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have signature := readDataOptional_part [57, 51] [56, 57] record.signature tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, messageEncoding, lastMsgSeqNumProcessed, sendingTime, origSendingTime, xmlData, noHops, signature, some_bind] <;> rfl

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
                  (paired_cons pairing _ _ (paired_optional pairing [51, 52, 55] record.messageEncoding (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [51, 54, 57] record.lastMsgSeqNumProcessed (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_dataOptional pairing [50, 49, 50] [50, 49, 51] record.xmlData (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_group pairing [54, 50, 55] NoHops.members NoHops.encode NoHops.within (by decide) (by decide) NoHops.taken record.noHops)
                        (paired_cons pairing _ _ (paired_dataOptional pairing [57, 51] [56, 57] record.signature (by decide) (by decide))
                         (paired_none pairing)))))))))))))))))))))))

structure Heartbeat where
  testReqID : Terminated 1  -- tag 112

def Heartbeat.parts (record : Heartbeat) : List Part :=
  [Part.required [49, 49, 50] record.testReqID]

def Heartbeat.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (tokens : List Token) : Option Heartbeat := do
  let testReqID ← readRequired [49, 49, 50] tokens
  pure { testReqID }

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (agrees : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  have distinct : Heartbeat.tags.flatten.Nodup := by decide +kernel
  have testReqID := readRequired_part [49, 49, 50] record.testReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [Heartbeat.decode, testReqID, some_bind] <;> rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 50] record.testReqID (by decide) (by decide))
   (paired_none pairing)

structure NoMsgTypes where
  refMsgType : Terminated 1  -- tag 372
  msgDirection : Option (Terminated 1)  -- tag 385

def NoMsgTypes.parts (record : NoMsgTypes) : List Part :=
  [Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 56, 53] record.msgDirection]

def NoMsgTypes.tags : List (List (List UInt8)) :=
  [[[51, 55, 50]], [[51, 56, 53]]]

theorem NoMsgTypes.shape (record : NoMsgTypes) : record.parts.map Part.tags = NoMsgTypes.tags := rfl

def NoMsgTypes.decode (tokens : List Token) : Option NoMsgTypes := do
  let refMsgType ← readRequired [51, 55, 50] tokens
  let msgDirection ← readOptional [51, 56, 53] tokens
  pure { refMsgType, msgDirection }

theorem NoMsgTypes.decode_agrees (record : NoMsgTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMsgTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMsgTypes.decode tokens = some record := by
  have distinct : NoMsgTypes.tags.flatten.Nodup := by decide +kernel
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have msgDirection := readOptional_part [51, 56, 53] record.msgDirection tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoMsgTypes.decode, refMsgType, msgDirection, some_bind] <;> rfl

theorem NoMsgTypes.taken (record : NoMsgTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 56, 53] record.msgDirection (by decide) (by decide))
    (paired_none pairing))

def NoMsgTypes.members : List (List UInt8) := NoMsgTypes.tags.flatten

def NoMsgTypes.encode (entry : NoMsgTypes) : List Token := encodeParts entry.parts

theorem NoMsgTypes.decode_encode (entry : NoMsgTypes) : NoMsgTypes.decode entry.encode = some entry :=
  NoMsgTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMsgTypes.within (entry : NoMsgTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoMsgTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMsgTypes.shape] at this

theorem NoMsgTypes.led (entry : NoMsgTypes) : Lead [51, 55, 50] entry.encode :=
  lead_parts [51, 55, 50] entry.refMsgType _ NoMsgTypes.tags.tail rfl (by decide +kernel)

structure Logon where
  encryptMethod : Terminated 1  -- tag 98
  heartBtInt : Terminated 1  -- tag 108
  rawData : Option (List UInt8)  -- tag 96
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  nextExpectedMsgSeqNum : Option (Terminated 1)  -- tag 789
  maxMessageSize : Option (Terminated 1)  -- tag 383
  noMsgTypes : List NoMsgTypes  -- tag 384
  testMessageIndicator : Option (Terminated 1)  -- tag 464
  username : Terminated 1  -- tag 553
  password : Terminated 1  -- tag 554

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.dataOptional [57, 53] [57, 54] record.rawData,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [55, 56, 57] record.nextExpectedMsgSeqNum,
   Part.optional [51, 56, 51] record.maxMessageSize,
   Part.group [51, 56, 52] NoMsgTypes.members NoMsgTypes.encode NoMsgTypes.within record.noMsgTypes,
   Part.optional [52, 54, 52] record.testMessageIndicator,
   Part.required [53, 53, 51] record.username,
   Part.required [53, 53, 52] record.password]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[57, 53], [57, 54]], [[49, 52, 49]], [[55, 56, 57]], [[51, 56, 51]], [51, 56, 52] :: NoMsgTypes.members, [[52, 54, 52]], [[53, 53, 51]], [[53, 53, 52]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let rawData ← readDataOptional [57, 53] [57, 54] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let nextExpectedMsgSeqNum ← readOptional [55, 56, 57] tokens
  let maxMessageSize ← readOptional [51, 56, 51] tokens
  let noMsgTypes ← readGroup [51, 56, 52] [51, 55, 50] NoMsgTypes.members NoMsgTypes.decode tokens
  let testMessageIndicator ← readOptional [52, 54, 52] tokens
  let username ← readRequired [53, 53, 51] tokens
  let password ← readRequired [53, 53, 52] tokens
  pure { encryptMethod, heartBtInt, rawData, resetSeqNumFlag, nextExpectedMsgSeqNum, maxMessageSize, noMsgTypes, testMessageIndicator, username, password }

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
  have nextExpectedMsgSeqNum := readOptional_part [55, 56, 57] record.nextExpectedMsgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have maxMessageSize := readOptional_part [51, 56, 51] record.maxMessageSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noMsgTypes := readGroup_part [51, 56, 52] [51, 55, 50] NoMsgTypes.members NoMsgTypes.encode NoMsgTypes.within NoMsgTypes.decode NoMsgTypes.decode_encode NoMsgTypes.led record.noMsgTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have testMessageIndicator := readOptional_part [52, 54, 52] record.testMessageIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have password := readRequired_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, rawData, resetSeqNumFlag, nextExpectedMsgSeqNum, maxMessageSize, noMsgTypes, testMessageIndicator, username, password, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_dataOptional pairing [57, 53] [57, 54] record.rawData (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [55, 56, 57] record.nextExpectedMsgSeqNum (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 56, 51] record.maxMessageSize (by decide) (by decide))
        (paired_cons pairing _ _ (paired_group pairing [51, 56, 52] NoMsgTypes.members NoMsgTypes.encode NoMsgTypes.within (by decide) (by decide) NoMsgTypes.taken record.noMsgTypes)
         (paired_cons pairing _ _ (paired_optional pairing [52, 54, 52] record.testMessageIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53, 52] record.password (by decide) (by decide))
            (paired_none pairing))))))))))

structure Logout where
  text : Option (Terminated 1)  -- tag 58
  encodedText : Option (List UInt8)  -- tag 355

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.dataOptional [51, 53, 52] [51, 53, 53] record.encodedText]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[51, 53, 52], [51, 53, 53]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  let encodedText ← readDataOptional [51, 53, 52] [51, 53, 53] tokens
  pure { text, encodedText }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have encodedText := readDataOptional_part [51, 53, 52] [51, 53, 53] record.encodedText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, text, encodedText, some_bind] <;> rfl

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_dataOptional pairing [51, 53, 52] [51, 53, 53] record.encodedText (by decide) (by decide))
    (paired_none pairing))

structure NoRelatedSym where
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[49, 54, 55]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  pure { symbol, securityType }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRelatedSym.decode, symbol, securityType, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
    (paired_none pairing))

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
  noRelatedSym : List NoRelatedSym  -- tag 146

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [49, 52, 54] :: NoRelatedSym.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let noRelatedSym ← readGroup [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { mDReqID, subscriptionRequestType, noRelatedSym }

theorem MarketDataRequest.decode_agrees (record : MarketDataRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequest.decode tokens = some record := by
  have distinct : MarketDataRequest.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [53, 53] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, noRelatedSym, some_bind] <;> rfl

theorem MarketDataRequest.taken (record : MarketDataRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
     (paired_none pairing)))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  text : Terminated 1  -- tag 58
  encodedText : Option (List UInt8)  -- tag 355
  sessionRejectReason : Terminated 1  -- tag 373

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.required [53, 56] record.text,
   Part.dataOptional [51, 53, 52] [51, 53, 53] record.encodedText,
   Part.required [51, 55, 51] record.sessionRejectReason]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[53, 56]], [[51, 53, 52], [51, 53, 53]], [[51, 55, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let text ← readRequired [53, 56] tokens
  let encodedText ← readDataOptional [51, 53, 52] [51, 53, 53] tokens
  let sessionRejectReason ← readRequired [51, 55, 51] tokens
  pure { refSeqNum, refTagID, refMsgType, text, encodedText, sessionRejectReason }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readOptional_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have encodedText := readDataOptional_part [51, 53, 52] [51, 53, 53] record.encodedText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have sessionRejectReason := readRequired_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, text, encodedText, sessionRejectReason, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
      (paired_cons pairing _ _ (paired_dataOptional pairing [51, 53, 52] [51, 53, 53] record.encodedText (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
        (paired_none pairing))))))

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

structure SecurityListRequest where
  securityReqID : Terminated 1  -- tag 320
  securityListRequestType : Terminated 1  -- tag 559
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202

def SecurityListRequest.parts (record : SecurityListRequest) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [53, 53, 57] record.securityListRequestType,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice]

def SecurityListRequest.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[53, 53, 57]], [[53, 53]], [[49, 54, 55]], [[55, 54, 50]], [[50, 48, 49]], [[50, 48, 50]]]

theorem SecurityListRequest.shape (record : SecurityListRequest) : record.parts.map Part.tags = SecurityListRequest.tags := rfl

def SecurityListRequest.decode (tokens : List Token) : Option SecurityListRequest := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityListRequestType ← readRequired [53, 53, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  pure { securityReqID, securityListRequestType, symbol, securityType, securitySubType, putOrCall, strikePrice }

theorem SecurityListRequest.decode_agrees (record : SecurityListRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityListRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityListRequest.decode tokens = some record := by
  have distinct : SecurityListRequest.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityListRequestType := readRequired_part [53, 53, 57] record.securityListRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [SecurityListRequest.decode, securityReqID, securityListRequestType, symbol, securityType, securitySubType, putOrCall, strikePrice, some_bind] <;> rfl

theorem SecurityListRequest.taken (record : SecurityListRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53, 57] record.securityListRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
         (paired_none pairing)))))))

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
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityListRequest (header : Header) (r0 : SecurityListRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], [86]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityListRequest header r0 => ⟨[51, 53], [120]⟩ :: encodeParts (header.parts ++ r0.parts)
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
      else if token.value = [86] then
        if known (Header.tags ++ MarketDataRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequest.decode rest
          pure (.marketDataRequest header r0)
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
      else if token.value = [120] then
        if known (Header.tags ++ SecurityListRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityListRequest.decode rest
          pure (.securityListRequest header r0)
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

theorem Message.decode_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decode (Message.tokens (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequest.tags) rfl
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

theorem Message.decode_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decode (Message.tokens (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityListRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityListRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityListRequest.tags) rfl
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
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityListRequest header r0 => exact Message.decode_securityListRequest header r0
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

theorem Message.decodeBytes_marketDataRequest (header : Header) (r0 : MarketDataRequest) :
    Message.decodeBytes (Message.encode (.marketDataRequest header r0)) = some (.marketDataRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [86]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequest header r0

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

theorem Message.decodeBytes_securityListRequest (header : Header) (r0 : SecurityListRequest) :
    Message.decodeBytes (Message.encode (.securityListRequest header r0)) = some (.securityListRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [120]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityListRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityListRequest header r0

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
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityListRequest header r0 => exact Message.decodeBytes_securityListRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseCoinbasederivativesMarketdataapiFixV027Client
