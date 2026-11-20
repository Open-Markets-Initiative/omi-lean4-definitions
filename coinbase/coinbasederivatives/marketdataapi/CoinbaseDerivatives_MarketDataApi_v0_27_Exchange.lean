import Wire

/-!
# Coinbase  v0.27, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

Note: SignatureLength and Signature stand in the trailer ahead of CheckSum: read by tag wherever they stand, as every field of a body is, and written after the header's other fields.

License: MIT No Attribution
-/

namespace Omi.CoinbaseCoinbasederivativesMarketdataapiFixV027Exchange

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

structure BusinessMessageReject where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  text : Option (Terminated 1)  -- tag 58
  businessRejectRefID : Option (Terminated 1)  -- tag 379
  businessRejectReason : Terminated 1  -- tag 380

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 57] record.businessRejectRefID,
   Part.required [51, 56, 48] record.businessRejectReason]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[53, 56]], [[51, 55, 57]], [[51, 56, 48]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let text ← readOptional [53, 56] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  pure { refSeqNum, refMsgType, text, businessRejectRefID, businessRejectReason }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, refMsgType, text, businessRejectRefID, businessRejectReason, some_bind] <;> rfl

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 57] record.businessRejectRefID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
       (paired_none pairing)))))

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

structure NoMDEntriesIncrementalRefresh where
  mDUpdateAction : Terminated 1  -- tag 279
  mDEntryType : Terminated 1  -- tag 269
  mDEntryID : Terminated 1  -- tag 278
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryDate : Option (Terminated 1)  -- tag 272
  mDEntryTime : Option (Terminated 1)  -- tag 273
  minQty : Option (Terminated 1)  -- tag 110
  transactTime : Terminated 1  -- tag 60
  mDPriceLevel : Option (Terminated 1)  -- tag 1023
  openCloseSettlFlag : Option (Terminated 1)  -- tag 286
  tradingReferenceDate : Option (Terminated 1)  -- tag 5796
  aggressorSide : Option (Terminated 1)  -- tag 5797
  trdType : Option (Terminated 1)  -- tag 828
  trdSubType : Option (Terminated 1)  -- tag 829
  differentialPrice : Option (Terminated 1)  -- tag 1522
  legLastPx : Option (Terminated 1)  -- tag 637

def NoMDEntriesIncrementalRefresh.parts (record : NoMDEntriesIncrementalRefresh) : List Part :=
  [Part.required [50, 55, 57] record.mDUpdateAction,
   Part.required [50, 54, 57] record.mDEntryType,
   Part.required [50, 55, 56] record.mDEntryID,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 55, 50] record.mDEntryDate,
   Part.optional [50, 55, 51] record.mDEntryTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 50, 51] record.mDPriceLevel,
   Part.optional [50, 56, 54] record.openCloseSettlFlag,
   Part.optional [53, 55, 57, 54] record.tradingReferenceDate,
   Part.optional [53, 55, 57, 55] record.aggressorSide,
   Part.optional [56, 50, 56] record.trdType,
   Part.optional [56, 50, 57] record.trdSubType,
   Part.optional [49, 53, 50, 50] record.differentialPrice,
   Part.optional [54, 51, 55] record.legLastPx]

def NoMDEntriesIncrementalRefresh.tags : List (List (List UInt8)) :=
  [[[50, 55, 57]], [[50, 54, 57]], [[50, 55, 56]], [[53, 53]], [[49, 54, 55]], [[55, 54, 50]], [[50, 48, 49]], [[50, 48, 50]], [[50, 55, 48]], [[50, 55, 49]], [[50, 55, 50]], [[50, 55, 51]], [[49, 49, 48]], [[54, 48]], [[49, 48, 50, 51]], [[50, 56, 54]], [[53, 55, 57, 54]], [[53, 55, 57, 55]], [[56, 50, 56]], [[56, 50, 57]], [[49, 53, 50, 50]], [[54, 51, 55]]]

theorem NoMDEntriesIncrementalRefresh.shape (record : NoMDEntriesIncrementalRefresh) : record.parts.map Part.tags = NoMDEntriesIncrementalRefresh.tags := rfl

def NoMDEntriesIncrementalRefresh.decode (tokens : List Token) : Option NoMDEntriesIncrementalRefresh := do
  let mDUpdateAction ← readRequired [50, 55, 57] tokens
  let mDEntryType ← readRequired [50, 54, 57] tokens
  let mDEntryID ← readRequired [50, 55, 56] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryDate ← readOptional [50, 55, 50] tokens
  let mDEntryTime ← readOptional [50, 55, 51] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let transactTime ← readRequired [54, 48] tokens
  let mDPriceLevel ← readOptional [49, 48, 50, 51] tokens
  let openCloseSettlFlag ← readOptional [50, 56, 54] tokens
  let tradingReferenceDate ← readOptional [53, 55, 57, 54] tokens
  let aggressorSide ← readOptional [53, 55, 57, 55] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  let trdSubType ← readOptional [56, 50, 57] tokens
  let differentialPrice ← readOptional [49, 53, 50, 50] tokens
  let legLastPx ← readOptional [54, 51, 55] tokens
  pure { mDUpdateAction, mDEntryType, mDEntryID, symbol, securityType, securitySubType, putOrCall, strikePrice, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, minQty, transactTime, mDPriceLevel, openCloseSettlFlag, tradingReferenceDate, aggressorSide, trdType, trdSubType, differentialPrice, legLastPx }

theorem NoMDEntriesIncrementalRefresh.decode_agrees (record : NoMDEntriesIncrementalRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntriesIncrementalRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntriesIncrementalRefresh.decode tokens = some record := by
  have distinct : NoMDEntriesIncrementalRefresh.tags.flatten.Nodup := by decide +kernel
  have mDUpdateAction := readRequired_part [50, 55, 57] record.mDUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntryID := readRequired_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have mDEntryDate := readOptional_part [50, 55, 50] record.mDEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have mDEntryTime := readOptional_part [50, 55, 51] record.mDEntryTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have mDPriceLevel := readOptional_part [49, 48, 50, 51] record.mDPriceLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have openCloseSettlFlag := readOptional_part [50, 56, 54] record.openCloseSettlFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have tradingReferenceDate := readOptional_part [53, 55, 57, 54] record.tradingReferenceDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have aggressorSide := readOptional_part [53, 55, 57, 55] record.aggressorSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have trdSubType := readOptional_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have differentialPrice := readOptional_part [49, 53, 50, 50] record.differentialPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have legLastPx := readOptional_part [54, 51, 55] record.legLastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  simp only [NoMDEntriesIncrementalRefresh.decode, mDUpdateAction, mDEntryType, mDEntryID, symbol, securityType, securitySubType, putOrCall, strikePrice, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, minQty, transactTime, mDPriceLevel, openCloseSettlFlag, tradingReferenceDate, aggressorSide, trdType, trdSubType, differentialPrice, legLastPx, some_bind] <;> rfl

theorem NoMDEntriesIncrementalRefresh.taken (record : NoMDEntriesIncrementalRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 55, 57] record.mDUpdateAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 55, 56] record.mDEntryID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48] record.mDEntryPx (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 55, 49] record.mDEntrySize (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 55, 50] record.mDEntryDate (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 55, 51] record.mDEntryTime (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50, 51] record.mDPriceLevel (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [50, 56, 54] record.openCloseSettlFlag (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 54] record.tradingReferenceDate (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 55] record.aggressorSide (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [56, 50, 56] record.trdType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [56, 50, 57] record.trdSubType (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [49, 53, 50, 50] record.differentialPrice (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [54, 51, 55] record.legLastPx (by decide) (by decide))
                        (paired_none pairing))))))))))))))))))))))

def NoMDEntriesIncrementalRefresh.members : List (List UInt8) := NoMDEntriesIncrementalRefresh.tags.flatten

def NoMDEntriesIncrementalRefresh.encode (entry : NoMDEntriesIncrementalRefresh) : List Token := encodeParts entry.parts

theorem NoMDEntriesIncrementalRefresh.decode_encode (entry : NoMDEntriesIncrementalRefresh) : NoMDEntriesIncrementalRefresh.decode entry.encode = some entry :=
  NoMDEntriesIncrementalRefresh.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntriesIncrementalRefresh.within (entry : NoMDEntriesIncrementalRefresh) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntriesIncrementalRefresh.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntriesIncrementalRefresh.shape] at this

theorem NoMDEntriesIncrementalRefresh.led (entry : NoMDEntriesIncrementalRefresh) : Lead [50, 55, 57] entry.encode :=
  lead_parts [50, 55, 57] entry.mDUpdateAction _ NoMDEntriesIncrementalRefresh.tags.tail rfl (by decide +kernel)

structure MarketDataIncrementalRefresh where
  mDReqID : Terminated 1  -- tag 262
  aggregatedBook : Terminated 1  -- tag 266
  noMDEntriesIncrementalRefresh : List NoMDEntriesIncrementalRefresh  -- tag 268

def MarketDataIncrementalRefresh.parts (record : MarketDataIncrementalRefresh) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 54] record.aggregatedBook,
   Part.group [50, 54, 56] NoMDEntriesIncrementalRefresh.members NoMDEntriesIncrementalRefresh.encode NoMDEntriesIncrementalRefresh.within record.noMDEntriesIncrementalRefresh]

def MarketDataIncrementalRefresh.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 54]], [50, 54, 56] :: NoMDEntriesIncrementalRefresh.members]

theorem MarketDataIncrementalRefresh.shape (record : MarketDataIncrementalRefresh) : record.parts.map Part.tags = MarketDataIncrementalRefresh.tags := rfl

def MarketDataIncrementalRefresh.decode (tokens : List Token) : Option MarketDataIncrementalRefresh := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let aggregatedBook ← readRequired [50, 54, 54] tokens
  let noMDEntriesIncrementalRefresh ← readGroup [50, 54, 56] [50, 55, 57] NoMDEntriesIncrementalRefresh.members NoMDEntriesIncrementalRefresh.decode tokens
  pure { mDReqID, aggregatedBook, noMDEntriesIncrementalRefresh }

theorem MarketDataIncrementalRefresh.decode_agrees (record : MarketDataIncrementalRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataIncrementalRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataIncrementalRefresh.decode tokens = some record := by
  have distinct : MarketDataIncrementalRefresh.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have aggregatedBook := readRequired_part [50, 54, 54] record.aggregatedBook tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noMDEntriesIncrementalRefresh := readGroup_part [50, 54, 56] [50, 55, 57] NoMDEntriesIncrementalRefresh.members NoMDEntriesIncrementalRefresh.encode NoMDEntriesIncrementalRefresh.within NoMDEntriesIncrementalRefresh.decode NoMDEntriesIncrementalRefresh.decode_encode NoMDEntriesIncrementalRefresh.led record.noMDEntriesIncrementalRefresh tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [MarketDataIncrementalRefresh.decode, mDReqID, aggregatedBook, noMDEntriesIncrementalRefresh, some_bind] <;> rfl

theorem MarketDataIncrementalRefresh.taken (record : MarketDataIncrementalRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 54] record.aggregatedBook (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntriesIncrementalRefresh.members NoMDEntriesIncrementalRefresh.encode NoMDEntriesIncrementalRefresh.within (by decide) (by decide) NoMDEntriesIncrementalRefresh.taken record.noMDEntriesIncrementalRefresh)
     (paired_none pairing)))

structure MarketDataRequestReject where
  mDReqID : Terminated 1  -- tag 262
  mDReqRejReason : Option (Terminated 1)  -- tag 281
  text : Option (Terminated 1)  -- tag 58

def MarketDataRequestReject.parts (record : MarketDataRequestReject) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.optional [50, 56, 49] record.mDReqRejReason,
   Part.optional [53, 56] record.text]

def MarketDataRequestReject.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 56, 49]], [[53, 56]]]

theorem MarketDataRequestReject.shape (record : MarketDataRequestReject) : record.parts.map Part.tags = MarketDataRequestReject.tags := rfl

def MarketDataRequestReject.decode (tokens : List Token) : Option MarketDataRequestReject := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let mDReqRejReason ← readOptional [50, 56, 49] tokens
  let text ← readOptional [53, 56] tokens
  pure { mDReqID, mDReqRejReason, text }

theorem MarketDataRequestReject.decode_agrees (record : MarketDataRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequestReject.decode tokens = some record := by
  have distinct : MarketDataRequestReject.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDReqRejReason := readOptional_part [50, 56, 49] record.mDReqRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [MarketDataRequestReject.decode, mDReqID, mDReqRejReason, text, some_bind] <;> rfl

theorem MarketDataRequestReject.taken (record : MarketDataRequestReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 56, 49] record.mDReqRejReason (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_none pairing)))

structure NoMDEntries where
  mDEntryType : Terminated 1  -- tag 269
  mDEntryID : Option (Terminated 1)  -- tag 278
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryDate : Option (Terminated 1)  -- tag 272
  mDEntryTime : Option (Terminated 1)  -- tag 273
  minQty : Option (Terminated 1)  -- tag 110
  transactTime : Terminated 1  -- tag 60
  mDPriceLevel : Option (Terminated 1)  -- tag 1023
  openCloseSettlFlag : Option (Terminated 1)  -- tag 286
  tradingReferenceDate : Option (Terminated 1)  -- tag 5796
  trdType : Option (Terminated 1)  -- tag 828

def NoMDEntries.parts (record : NoMDEntries) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType,
   Part.optional [50, 55, 56] record.mDEntryID,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 55, 50] record.mDEntryDate,
   Part.optional [50, 55, 51] record.mDEntryTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 50, 51] record.mDPriceLevel,
   Part.optional [50, 56, 54] record.openCloseSettlFlag,
   Part.optional [53, 55, 57, 54] record.tradingReferenceDate,
   Part.optional [56, 50, 56] record.trdType]

def NoMDEntries.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]], [[50, 55, 56]], [[50, 55, 48]], [[50, 55, 49]], [[50, 55, 50]], [[50, 55, 51]], [[49, 49, 48]], [[54, 48]], [[49, 48, 50, 51]], [[50, 56, 54]], [[53, 55, 57, 54]], [[56, 50, 56]]]

theorem NoMDEntries.shape (record : NoMDEntries) : record.parts.map Part.tags = NoMDEntries.tags := rfl

def NoMDEntries.decode (tokens : List Token) : Option NoMDEntries := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  let mDEntryID ← readOptional [50, 55, 56] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryDate ← readOptional [50, 55, 50] tokens
  let mDEntryTime ← readOptional [50, 55, 51] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let transactTime ← readRequired [54, 48] tokens
  let mDPriceLevel ← readOptional [49, 48, 50, 51] tokens
  let openCloseSettlFlag ← readOptional [50, 56, 54] tokens
  let tradingReferenceDate ← readOptional [53, 55, 57, 54] tokens
  let trdType ← readOptional [56, 50, 56] tokens
  pure { mDEntryType, mDEntryID, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, minQty, transactTime, mDPriceLevel, openCloseSettlFlag, tradingReferenceDate, trdType }

theorem NoMDEntries.decode_agrees (record : NoMDEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntries.decode tokens = some record := by
  have distinct : NoMDEntries.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryID := readOptional_part [50, 55, 56] record.mDEntryID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have mDEntryDate := readOptional_part [50, 55, 50] record.mDEntryDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have mDEntryTime := readOptional_part [50, 55, 51] record.mDEntryTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have mDPriceLevel := readOptional_part [49, 48, 50, 51] record.mDPriceLevel tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have openCloseSettlFlag := readOptional_part [50, 56, 54] record.openCloseSettlFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have tradingReferenceDate := readOptional_part [53, 55, 57, 54] record.tradingReferenceDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have trdType := readOptional_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [NoMDEntries.decode, mDEntryType, mDEntryID, mDEntryPx, mDEntrySize, mDEntryDate, mDEntryTime, minQty, transactTime, mDPriceLevel, openCloseSettlFlag, tradingReferenceDate, trdType, some_bind] <;> rfl

theorem NoMDEntries.taken (record : NoMDEntries) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 55, 56] record.mDEntryID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48] record.mDEntryPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 55, 49] record.mDEntrySize (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 55, 50] record.mDEntryDate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 55, 51] record.mDEntryTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 50, 51] record.mDPriceLevel (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 56, 54] record.openCloseSettlFlag (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 54] record.tradingReferenceDate (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [56, 50, 56] record.trdType (by decide) (by decide))
              (paired_none pairing))))))))))))

def NoMDEntries.members : List (List UInt8) := NoMDEntries.tags.flatten

def NoMDEntries.encode (entry : NoMDEntries) : List Token := encodeParts entry.parts

theorem NoMDEntries.decode_encode (entry : NoMDEntries) : NoMDEntries.decode entry.encode = some entry :=
  NoMDEntries.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntries.within (entry : NoMDEntries) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntries.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntries.shape] at this

theorem NoMDEntries.led (entry : NoMDEntries) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMDEntries.tags.tail rfl (by decide +kernel)

structure MarketDataSnapshotFullRefresh where
  mDReqID : Terminated 1  -- tag 262
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  noMDEntries : List NoMDEntries  -- tag 268

def MarketDataSnapshotFullRefresh.parts (record : MarketDataSnapshotFullRefresh) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.group [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within record.noMDEntries]

def MarketDataSnapshotFullRefresh.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[53, 53]], [[49, 54, 55]], [[55, 54, 50]], [[50, 48, 49]], [[50, 48, 50]], [50, 54, 56] :: NoMDEntries.members]

theorem MarketDataSnapshotFullRefresh.shape (record : MarketDataSnapshotFullRefresh) : record.parts.map Part.tags = MarketDataSnapshotFullRefresh.tags := rfl

def MarketDataSnapshotFullRefresh.decode (tokens : List Token) : Option MarketDataSnapshotFullRefresh := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let noMDEntries ← readGroup [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.decode tokens
  pure { mDReqID, symbol, securityType, securitySubType, putOrCall, strikePrice, noMDEntries }

theorem MarketDataSnapshotFullRefresh.decode_agrees (record : MarketDataSnapshotFullRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataSnapshotFullRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataSnapshotFullRefresh.decode tokens = some record := by
  have distinct : MarketDataSnapshotFullRefresh.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have noMDEntries := readGroup_part [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.encode NoMDEntries.within NoMDEntries.decode NoMDEntries.decode_encode NoMDEntries.led record.noMDEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [MarketDataSnapshotFullRefresh.decode, mDReqID, symbol, securityType, securitySubType, putOrCall, strikePrice, noMDEntries, some_bind] <;> rfl

theorem MarketDataSnapshotFullRefresh.taken (record : MarketDataSnapshotFullRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
        (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within (by decide) (by decide) NoMDEntries.taken record.noMDEntries)
         (paired_none pairing)))))))

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

structure NoEvents where
  eventType : Terminated 1  -- tag 865
  eventTime : Terminated 1  -- tag 1145

def NoEvents.parts (record : NoEvents) : List Part :=
  [Part.required [56, 54, 53] record.eventType,
   Part.required [49, 49, 52, 53] record.eventTime]

def NoEvents.tags : List (List (List UInt8)) :=
  [[[56, 54, 53]], [[49, 49, 52, 53]]]

theorem NoEvents.shape (record : NoEvents) : record.parts.map Part.tags = NoEvents.tags := rfl

def NoEvents.decode (tokens : List Token) : Option NoEvents := do
  let eventType ← readRequired [56, 54, 53] tokens
  let eventTime ← readRequired [49, 49, 52, 53] tokens
  pure { eventType, eventTime }

theorem NoEvents.decode_agrees (record : NoEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoEvents.decode tokens = some record := by
  have distinct : NoEvents.tags.flatten.Nodup := by decide +kernel
  have eventType := readRequired_part [56, 54, 53] record.eventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have eventTime := readRequired_part [49, 49, 52, 53] record.eventTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoEvents.decode, eventType, eventTime, some_bind] <;> rfl

theorem NoEvents.taken (record : NoEvents) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [56, 54, 53] record.eventType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49, 52, 53] record.eventTime (by decide) (by decide))
    (paired_none pairing))

def NoEvents.members : List (List UInt8) := NoEvents.tags.flatten

def NoEvents.encode (entry : NoEvents) : List Token := encodeParts entry.parts

theorem NoEvents.decode_encode (entry : NoEvents) : NoEvents.decode entry.encode = some entry :=
  NoEvents.decode_agrees entry _ (fun _ _ => rfl)

theorem NoEvents.within (entry : NoEvents) : ∀ token ∈ entry.encode, token.tag ∈ NoEvents.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoEvents.shape] at this

theorem NoEvents.led (entry : NoEvents) : Lead [56, 54, 53] entry.encode :=
  lead_parts [56, 54, 53] entry.eventType _ NoEvents.tags.tail rfl (by decide +kernel)

structure NoLegs where
  legSymbol : Terminated 1  -- tag 600
  legSecurityDesc : Option (Terminated 1)  -- tag 620
  legSecurityType : Option (Terminated 1)  -- tag 609
  legSide : Option (Terminated 1)  -- tag 624
  legCFICode : Option (Terminated 1)  -- tag 608
  legCurrency : Option (Terminated 1)  -- tag 556

def NoLegs.parts (record : NoLegs) : List Part :=
  [Part.required [54, 48, 48] record.legSymbol,
   Part.optional [54, 50, 48] record.legSecurityDesc,
   Part.optional [54, 48, 57] record.legSecurityType,
   Part.optional [54, 50, 52] record.legSide,
   Part.optional [54, 48, 56] record.legCFICode,
   Part.optional [53, 53, 54] record.legCurrency]

def NoLegs.tags : List (List (List UInt8)) :=
  [[[54, 48, 48]], [[54, 50, 48]], [[54, 48, 57]], [[54, 50, 52]], [[54, 48, 56]], [[53, 53, 54]]]

theorem NoLegs.shape (record : NoLegs) : record.parts.map Part.tags = NoLegs.tags := rfl

def NoLegs.decode (tokens : List Token) : Option NoLegs := do
  let legSymbol ← readRequired [54, 48, 48] tokens
  let legSecurityDesc ← readOptional [54, 50, 48] tokens
  let legSecurityType ← readOptional [54, 48, 57] tokens
  let legSide ← readOptional [54, 50, 52] tokens
  let legCFICode ← readOptional [54, 48, 56] tokens
  let legCurrency ← readOptional [53, 53, 54] tokens
  pure { legSymbol, legSecurityDesc, legSecurityType, legSide, legCFICode, legCurrency }

theorem NoLegs.decode_agrees (record : NoLegs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLegs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLegs.decode tokens = some record := by
  have distinct : NoLegs.tags.flatten.Nodup := by decide +kernel
  have legSymbol := readRequired_part [54, 48, 48] record.legSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have legSecurityDesc := readOptional_part [54, 50, 48] record.legSecurityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have legSecurityType := readOptional_part [54, 48, 57] record.legSecurityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have legSide := readOptional_part [54, 50, 52] record.legSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have legCFICode := readOptional_part [54, 48, 56] record.legCFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have legCurrency := readOptional_part [53, 53, 54] record.legCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [NoLegs.decode, legSymbol, legSecurityDesc, legSecurityType, legSide, legCFICode, legCurrency, some_bind] <;> rfl

theorem NoLegs.taken (record : NoLegs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 48, 48] record.legSymbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 50, 48] record.legSecurityDesc (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [54, 48, 57] record.legSecurityType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [54, 50, 52] record.legSide (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 48, 56] record.legCFICode (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 53, 54] record.legCurrency (by decide) (by decide))
        (paired_none pairing))))))

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

structure SecurityDefinition where
  securityUpdateAction : Terminated 1  -- tag 980
  lastUpdateTime : Terminated 1  -- tag 779
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  securityDesc : Terminated 1  -- tag 107
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  asset : Terminated 1  -- tag 6937
  cFICode : Terminated 1  -- tag 461
  underlyingProduct : Terminated 1  -- tag 462
  mDSecurityTradingStatus : Option (Terminated 1)  -- tag 1682
  haltReason : Option (Terminated 1)  -- tag 327
  currency : Terminated 1  -- tag 15
  settlCurrency : Option (Terminated 1)  -- tag 120
  minTradeVol : Terminated 1  -- tag 562
  maxTradeVol : Terminated 1  -- tag 1140
  minPriceIncrement : Terminated 1  -- tag 969
  largeTickThreshold : Option (Terminated 1)  -- tag 29001
  largeTick : Option (Terminated 1)  -- tag 29002
  noEvents : List NoEvents  -- tag 864
  contractMultiplier : Option (Terminated 1)  -- tag 231
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  unitOfMeasureQty : Option (Terminated 1)  -- tag 1147
  highLimitPrice : Option (Terminated 1)  -- tag 1149
  lowLimitPrice : Option (Terminated 1)  -- tag 1148
  maxPriceVariation : Option (Terminated 1)  -- tag 1143
  tradingReferenceDate : Option (Terminated 1)  -- tag 5796
  openInterestQty : Option (Terminated 1)  -- tag 5792
  clearedVolume : Option (Terminated 1)  -- tag 5791
  fundingRateApplicable : Option (Terminated 1)  -- tag 9001
  fundingInterval : Option (Terminated 1)  -- tag 9002
  fairValueLimit : Option (Terminated 1)  -- tag 9003
  priorSettlPrice : Option (Terminated 1)  -- tag 734
  settlPrice : Option (Terminated 1)  -- tag 730
  settlPriceType : Option (Terminated 1)  -- tag 731
  noUnderlyings : Option (Terminated 1)  -- tag 711
  underlyingSymbol : Option (Terminated 1)  -- tag 311
  noLegs : List NoLegs  -- tag 555

def SecurityDefinition.parts (record : SecurityDefinition) : List Part :=
  [Part.required [57, 56, 48] record.securityUpdateAction,
   Part.required [55, 55, 57] record.lastUpdateTime,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.required [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [54, 57, 51, 55] record.asset,
   Part.required [52, 54, 49] record.cFICode,
   Part.required [52, 54, 50] record.underlyingProduct,
   Part.optional [49, 54, 56, 50] record.mDSecurityTradingStatus,
   Part.optional [51, 50, 55] record.haltReason,
   Part.required [49, 53] record.currency,
   Part.optional [49, 50, 48] record.settlCurrency,
   Part.required [53, 54, 50] record.minTradeVol,
   Part.required [49, 49, 52, 48] record.maxTradeVol,
   Part.required [57, 54, 57] record.minPriceIncrement,
   Part.optional [50, 57, 48, 48, 49] record.largeTickThreshold,
   Part.optional [50, 57, 48, 48, 50] record.largeTick,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQty,
   Part.optional [49, 49, 52, 57] record.highLimitPrice,
   Part.optional [49, 49, 52, 56] record.lowLimitPrice,
   Part.optional [49, 49, 52, 51] record.maxPriceVariation,
   Part.optional [53, 55, 57, 54] record.tradingReferenceDate,
   Part.optional [53, 55, 57, 50] record.openInterestQty,
   Part.optional [53, 55, 57, 49] record.clearedVolume,
   Part.optional [57, 48, 48, 49] record.fundingRateApplicable,
   Part.optional [57, 48, 48, 50] record.fundingInterval,
   Part.optional [57, 48, 48, 51] record.fairValueLimit,
   Part.optional [55, 51, 52] record.priorSettlPrice,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.optional [55, 51, 49] record.settlPriceType,
   Part.optional [55, 49, 49] record.noUnderlyings,
   Part.optional [51, 49, 49] record.underlyingSymbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def SecurityDefinition.tags : List (List (List UInt8)) :=
  [[[57, 56, 48]], [[55, 55, 57]], [[53, 53]], [[49, 54, 55]], [[55, 54, 50]], [[49, 48, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[54, 57, 51, 55]], [[52, 54, 49]], [[52, 54, 50]], [[49, 54, 56, 50]], [[51, 50, 55]], [[49, 53]], [[49, 50, 48]], [[53, 54, 50]], [[49, 49, 52, 48]], [[57, 54, 57]], [[50, 57, 48, 48, 49]], [[50, 57, 48, 48, 50]], [56, 54, 52] :: NoEvents.members, [[50, 51, 49]], [[57, 57, 54]], [[49, 49, 52, 55]], [[49, 49, 52, 57]], [[49, 49, 52, 56]], [[49, 49, 52, 51]], [[53, 55, 57, 54]], [[53, 55, 57, 50]], [[53, 55, 57, 49]], [[57, 48, 48, 49]], [[57, 48, 48, 50]], [[57, 48, 48, 51]], [[55, 51, 52]], [[55, 51, 48]], [[55, 51, 49]], [[55, 49, 49]], [[51, 49, 49]], [53, 53, 53] :: NoLegs.members]

theorem SecurityDefinition.shape (record : SecurityDefinition) : record.parts.map Part.tags = SecurityDefinition.tags := rfl

def SecurityDefinition.decode (tokens : List Token) : Option SecurityDefinition := do
  let securityUpdateAction ← readRequired [57, 56, 48] tokens
  let lastUpdateTime ← readRequired [55, 55, 57] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let securityDesc ← readRequired [49, 48, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let asset ← readRequired [54, 57, 51, 55] tokens
  let cFICode ← readRequired [52, 54, 49] tokens
  let underlyingProduct ← readRequired [52, 54, 50] tokens
  let mDSecurityTradingStatus ← readOptional [49, 54, 56, 50] tokens
  let haltReason ← readOptional [51, 50, 55] tokens
  let currency ← readRequired [49, 53] tokens
  let settlCurrency ← readOptional [49, 50, 48] tokens
  let minTradeVol ← readRequired [53, 54, 50] tokens
  let maxTradeVol ← readRequired [49, 49, 52, 48] tokens
  let minPriceIncrement ← readRequired [57, 54, 57] tokens
  let largeTickThreshold ← readOptional [50, 57, 48, 48, 49] tokens
  let largeTick ← readOptional [50, 57, 48, 48, 50] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let unitOfMeasureQty ← readOptional [49, 49, 52, 55] tokens
  let highLimitPrice ← readOptional [49, 49, 52, 57] tokens
  let lowLimitPrice ← readOptional [49, 49, 52, 56] tokens
  let maxPriceVariation ← readOptional [49, 49, 52, 51] tokens
  let tradingReferenceDate ← readOptional [53, 55, 57, 54] tokens
  let openInterestQty ← readOptional [53, 55, 57, 50] tokens
  let clearedVolume ← readOptional [53, 55, 57, 49] tokens
  let fundingRateApplicable ← readOptional [57, 48, 48, 49] tokens
  let fundingInterval ← readOptional [57, 48, 48, 50] tokens
  let fairValueLimit ← readOptional [57, 48, 48, 51] tokens
  let priorSettlPrice ← readOptional [55, 51, 52] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let settlPriceType ← readOptional [55, 51, 49] tokens
  let noUnderlyings ← readOptional [55, 49, 49] tokens
  let underlyingSymbol ← readOptional [51, 49, 49] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { securityUpdateAction, lastUpdateTime, symbol, securityType, securitySubType, securityDesc, maturityMonthYear, putOrCall, strikePrice, asset, cFICode, underlyingProduct, mDSecurityTradingStatus, haltReason, currency, settlCurrency, minTradeVol, maxTradeVol, minPriceIncrement, largeTickThreshold, largeTick, noEvents, contractMultiplier, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, tradingReferenceDate, openInterestQty, clearedVolume, fundingRateApplicable, fundingInterval, fairValueLimit, priorSettlPrice, settlPrice, settlPriceType, noUnderlyings, underlyingSymbol, noLegs }

theorem SecurityDefinition.decode_agrees (record : SecurityDefinition) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityDefinition.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityDefinition.decode tokens = some record := by
  have distinct : SecurityDefinition.tags.flatten.Nodup := by decide +kernel
  have securityUpdateAction := readRequired_part [57, 56, 48] record.securityUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have lastUpdateTime := readRequired_part [55, 55, 57] record.lastUpdateTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityDesc := readRequired_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have asset := readRequired_part [54, 57, 51, 55] record.asset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have cFICode := readRequired_part [52, 54, 49] record.cFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have underlyingProduct := readRequired_part [52, 54, 50] record.underlyingProduct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have mDSecurityTradingStatus := readOptional_part [49, 54, 56, 50] record.mDSecurityTradingStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have haltReason := readOptional_part [51, 50, 55] record.haltReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have settlCurrency := readOptional_part [49, 50, 48] record.settlCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have minTradeVol := readRequired_part [53, 54, 50] record.minTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maxTradeVol := readRequired_part [49, 49, 52, 48] record.maxTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have minPriceIncrement := readRequired_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have largeTickThreshold := readOptional_part [50, 57, 48, 48, 49] record.largeTickThreshold tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have largeTick := readOptional_part [50, 57, 48, 48, 50] record.largeTick tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have unitOfMeasureQty := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have highLimitPrice := readOptional_part [49, 49, 52, 57] record.highLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have lowLimitPrice := readOptional_part [49, 49, 52, 56] record.lowLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have maxPriceVariation := readOptional_part [49, 49, 52, 51] record.maxPriceVariation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tradingReferenceDate := readOptional_part [53, 55, 57, 54] record.tradingReferenceDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have openInterestQty := readOptional_part [53, 55, 57, 50] record.openInterestQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have clearedVolume := readOptional_part [53, 55, 57, 49] record.clearedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have fundingRateApplicable := readOptional_part [57, 48, 48, 49] record.fundingRateApplicable tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have fundingInterval := readOptional_part [57, 48, 48, 50] record.fundingInterval tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have fairValueLimit := readOptional_part [57, 48, 48, 51] record.fairValueLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have priorSettlPrice := readOptional_part [55, 51, 52] record.priorSettlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have settlPriceType := readOptional_part [55, 51, 49] record.settlPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have noUnderlyings := readOptional_part [55, 49, 49] record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have underlyingSymbol := readOptional_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  simp only [SecurityDefinition.decode, securityUpdateAction, lastUpdateTime, symbol, securityType, securitySubType, securityDesc, maturityMonthYear, putOrCall, strikePrice, asset, cFICode, underlyingProduct, mDSecurityTradingStatus, haltReason, currency, settlCurrency, minTradeVol, maxTradeVol, minPriceIncrement, largeTickThreshold, largeTick, noEvents, contractMultiplier, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, tradingReferenceDate, openInterestQty, clearedVolume, fundingRateApplicable, fundingInterval, fairValueLimit, priorSettlPrice, settlPrice, settlPriceType, noUnderlyings, underlyingSymbol, noLegs, some_bind] <;> rfl

theorem SecurityDefinition.taken (record : SecurityDefinition) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56, 48] record.securityUpdateAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [55, 55, 57] record.lastUpdateTime (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [54, 57, 51, 55] record.asset (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [52, 54, 49] record.cFICode (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 54, 50] record.underlyingProduct (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 54, 56, 50] record.mDSecurityTradingStatus (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [51, 50, 55] record.haltReason (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48] record.settlCurrency (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [53, 54, 50] record.minTradeVol (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [49, 49, 52, 48] record.maxTradeVol (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 57, 48, 48, 49] record.largeTickThreshold (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 57, 48, 48, 50] record.largeTick (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_group pairing [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within (by decide) (by decide) NoEvents.taken record.noEvents)
                        (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [57, 57, 54] record.unitOfMeasure (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 55] record.unitOfMeasureQty (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 57] record.highLimitPrice (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 56] record.lowLimitPrice (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 51] record.maxPriceVariation (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 54] record.tradingReferenceDate (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 50] record.openInterestQty (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 49] record.clearedVolume (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 49] record.fundingRateApplicable (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 50] record.fundingInterval (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 51] record.fairValueLimit (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [55, 51, 52] record.priorSettlPrice (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [55, 51, 48] record.settlPrice (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [55, 51, 49] record.settlPriceType (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [55, 49, 49] record.noUnderlyings (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                                          (paired_none pairing))))))))))))))))))))))))))))))))))))))))

structure NoRelatedSymSecListGrp where
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  securitySubType : Option (Terminated 1)  -- tag 762
  securityDesc : Terminated 1  -- tag 107
  maturityMonthYear : Option (Terminated 1)  -- tag 200
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  asset : Terminated 1  -- tag 6937
  cFICode : Terminated 1  -- tag 461
  underlyingProduct : Terminated 1  -- tag 462
  mDSecurityTradingStatus : Option (Terminated 1)  -- tag 1682
  haltReason : Option (Terminated 1)  -- tag 327
  currency : Terminated 1  -- tag 15
  settlCurrency : Option (Terminated 1)  -- tag 120
  minTradeVol : Terminated 1  -- tag 562
  maxTradeVol : Terminated 1  -- tag 1140
  minPriceIncrement : Terminated 1  -- tag 969
  largeTickThreshold : Option (Terminated 1)  -- tag 29001
  largeTick : Option (Terminated 1)  -- tag 29002
  noEvents : List NoEvents  -- tag 864
  contractMultiplier : Option (Terminated 1)  -- tag 231
  unitOfMeasure : Option (Terminated 1)  -- tag 996
  unitOfMeasureQty : Option (Terminated 1)  -- tag 1147
  highLimitPrice : Option (Terminated 1)  -- tag 1149
  lowLimitPrice : Option (Terminated 1)  -- tag 1148
  maxPriceVariation : Option (Terminated 1)  -- tag 1143
  tradingReferenceDate : Option (Terminated 1)  -- tag 5796
  openInterestQty : Option (Terminated 1)  -- tag 5792
  clearedVolume : Option (Terminated 1)  -- tag 5791
  fundingRateApplicable : Option (Terminated 1)  -- tag 9001
  fundingInterval : Option (Terminated 1)  -- tag 9002
  fairValueLimit : Option (Terminated 1)  -- tag 9003
  priorSettlPrice : Option (Terminated 1)  -- tag 734
  settlPrice : Option (Terminated 1)  -- tag 730
  settlPriceType : Option (Terminated 1)  -- tag 731
  noUnderlyings : Option (Terminated 1)  -- tag 711
  underlyingSymbol : Option (Terminated 1)  -- tag 311
  noLegs : List NoLegs  -- tag 555

def NoRelatedSymSecListGrp.parts (record : NoRelatedSymSecListGrp) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [55, 54, 50] record.securitySubType,
   Part.required [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 48] record.maturityMonthYear,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [54, 57, 51, 55] record.asset,
   Part.required [52, 54, 49] record.cFICode,
   Part.required [52, 54, 50] record.underlyingProduct,
   Part.optional [49, 54, 56, 50] record.mDSecurityTradingStatus,
   Part.optional [51, 50, 55] record.haltReason,
   Part.required [49, 53] record.currency,
   Part.optional [49, 50, 48] record.settlCurrency,
   Part.required [53, 54, 50] record.minTradeVol,
   Part.required [49, 49, 52, 48] record.maxTradeVol,
   Part.required [57, 54, 57] record.minPriceIncrement,
   Part.optional [50, 57, 48, 48, 49] record.largeTickThreshold,
   Part.optional [50, 57, 48, 48, 50] record.largeTick,
   Part.group [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within record.noEvents,
   Part.optional [50, 51, 49] record.contractMultiplier,
   Part.optional [57, 57, 54] record.unitOfMeasure,
   Part.optional [49, 49, 52, 55] record.unitOfMeasureQty,
   Part.optional [49, 49, 52, 57] record.highLimitPrice,
   Part.optional [49, 49, 52, 56] record.lowLimitPrice,
   Part.optional [49, 49, 52, 51] record.maxPriceVariation,
   Part.optional [53, 55, 57, 54] record.tradingReferenceDate,
   Part.optional [53, 55, 57, 50] record.openInterestQty,
   Part.optional [53, 55, 57, 49] record.clearedVolume,
   Part.optional [57, 48, 48, 49] record.fundingRateApplicable,
   Part.optional [57, 48, 48, 50] record.fundingInterval,
   Part.optional [57, 48, 48, 51] record.fairValueLimit,
   Part.optional [55, 51, 52] record.priorSettlPrice,
   Part.optional [55, 51, 48] record.settlPrice,
   Part.optional [55, 51, 49] record.settlPriceType,
   Part.optional [55, 49, 49] record.noUnderlyings,
   Part.optional [51, 49, 49] record.underlyingSymbol,
   Part.group [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within record.noLegs]

def NoRelatedSymSecListGrp.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[49, 54, 55]], [[55, 54, 50]], [[49, 48, 55]], [[50, 48, 48]], [[50, 48, 49]], [[50, 48, 50]], [[54, 57, 51, 55]], [[52, 54, 49]], [[52, 54, 50]], [[49, 54, 56, 50]], [[51, 50, 55]], [[49, 53]], [[49, 50, 48]], [[53, 54, 50]], [[49, 49, 52, 48]], [[57, 54, 57]], [[50, 57, 48, 48, 49]], [[50, 57, 48, 48, 50]], [56, 54, 52] :: NoEvents.members, [[50, 51, 49]], [[57, 57, 54]], [[49, 49, 52, 55]], [[49, 49, 52, 57]], [[49, 49, 52, 56]], [[49, 49, 52, 51]], [[53, 55, 57, 54]], [[53, 55, 57, 50]], [[53, 55, 57, 49]], [[57, 48, 48, 49]], [[57, 48, 48, 50]], [[57, 48, 48, 51]], [[55, 51, 52]], [[55, 51, 48]], [[55, 51, 49]], [[55, 49, 49]], [[51, 49, 49]], [53, 53, 53] :: NoLegs.members]

theorem NoRelatedSymSecListGrp.shape (record : NoRelatedSymSecListGrp) : record.parts.map Part.tags = NoRelatedSymSecListGrp.tags := rfl

def NoRelatedSymSecListGrp.decode (tokens : List Token) : Option NoRelatedSymSecListGrp := do
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securitySubType ← readOptional [55, 54, 50] tokens
  let securityDesc ← readRequired [49, 48, 55] tokens
  let maturityMonthYear ← readOptional [50, 48, 48] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let asset ← readRequired [54, 57, 51, 55] tokens
  let cFICode ← readRequired [52, 54, 49] tokens
  let underlyingProduct ← readRequired [52, 54, 50] tokens
  let mDSecurityTradingStatus ← readOptional [49, 54, 56, 50] tokens
  let haltReason ← readOptional [51, 50, 55] tokens
  let currency ← readRequired [49, 53] tokens
  let settlCurrency ← readOptional [49, 50, 48] tokens
  let minTradeVol ← readRequired [53, 54, 50] tokens
  let maxTradeVol ← readRequired [49, 49, 52, 48] tokens
  let minPriceIncrement ← readRequired [57, 54, 57] tokens
  let largeTickThreshold ← readOptional [50, 57, 48, 48, 49] tokens
  let largeTick ← readOptional [50, 57, 48, 48, 50] tokens
  let noEvents ← readGroup [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.decode tokens
  let contractMultiplier ← readOptional [50, 51, 49] tokens
  let unitOfMeasure ← readOptional [57, 57, 54] tokens
  let unitOfMeasureQty ← readOptional [49, 49, 52, 55] tokens
  let highLimitPrice ← readOptional [49, 49, 52, 57] tokens
  let lowLimitPrice ← readOptional [49, 49, 52, 56] tokens
  let maxPriceVariation ← readOptional [49, 49, 52, 51] tokens
  let tradingReferenceDate ← readOptional [53, 55, 57, 54] tokens
  let openInterestQty ← readOptional [53, 55, 57, 50] tokens
  let clearedVolume ← readOptional [53, 55, 57, 49] tokens
  let fundingRateApplicable ← readOptional [57, 48, 48, 49] tokens
  let fundingInterval ← readOptional [57, 48, 48, 50] tokens
  let fairValueLimit ← readOptional [57, 48, 48, 51] tokens
  let priorSettlPrice ← readOptional [55, 51, 52] tokens
  let settlPrice ← readOptional [55, 51, 48] tokens
  let settlPriceType ← readOptional [55, 51, 49] tokens
  let noUnderlyings ← readOptional [55, 49, 49] tokens
  let underlyingSymbol ← readOptional [51, 49, 49] tokens
  let noLegs ← readGroup [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.decode tokens
  pure { symbol, securityType, securitySubType, securityDesc, maturityMonthYear, putOrCall, strikePrice, asset, cFICode, underlyingProduct, mDSecurityTradingStatus, haltReason, currency, settlCurrency, minTradeVol, maxTradeVol, minPriceIncrement, largeTickThreshold, largeTick, noEvents, contractMultiplier, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, tradingReferenceDate, openInterestQty, clearedVolume, fundingRateApplicable, fundingInterval, fairValueLimit, priorSettlPrice, settlPrice, settlPriceType, noUnderlyings, underlyingSymbol, noLegs }

theorem NoRelatedSymSecListGrp.decode_agrees (record : NoRelatedSymSecListGrp) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSymSecListGrp.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSymSecListGrp.decode tokens = some record := by
  have distinct : NoRelatedSymSecListGrp.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securitySubType := readOptional_part [55, 54, 50] record.securitySubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityDesc := readRequired_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have maturityMonthYear := readOptional_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have asset := readRequired_part [54, 57, 51, 55] record.asset tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have cFICode := readRequired_part [52, 54, 49] record.cFICode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have underlyingProduct := readRequired_part [52, 54, 50] record.underlyingProduct tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have mDSecurityTradingStatus := readOptional_part [49, 54, 56, 50] record.mDSecurityTradingStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have haltReason := readOptional_part [51, 50, 55] record.haltReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have settlCurrency := readOptional_part [49, 50, 48] record.settlCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minTradeVol := readRequired_part [53, 54, 50] record.minTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxTradeVol := readRequired_part [49, 49, 52, 48] record.maxTradeVol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have minPriceIncrement := readRequired_part [57, 54, 57] record.minPriceIncrement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have largeTickThreshold := readOptional_part [50, 57, 48, 48, 49] record.largeTickThreshold tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have largeTick := readOptional_part [50, 57, 48, 48, 50] record.largeTick tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noEvents := readGroup_part [56, 54, 52] [56, 54, 53] NoEvents.members NoEvents.encode NoEvents.within NoEvents.decode NoEvents.decode_encode NoEvents.led record.noEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have contractMultiplier := readOptional_part [50, 51, 49] record.contractMultiplier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have unitOfMeasure := readOptional_part [57, 57, 54] record.unitOfMeasure tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have unitOfMeasureQty := readOptional_part [49, 49, 52, 55] record.unitOfMeasureQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have highLimitPrice := readOptional_part [49, 49, 52, 57] record.highLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have lowLimitPrice := readOptional_part [49, 49, 52, 56] record.lowLimitPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have maxPriceVariation := readOptional_part [49, 49, 52, 51] record.maxPriceVariation tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have tradingReferenceDate := readOptional_part [53, 55, 57, 54] record.tradingReferenceDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have openInterestQty := readOptional_part [53, 55, 57, 50] record.openInterestQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have clearedVolume := readOptional_part [53, 55, 57, 49] record.clearedVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have fundingRateApplicable := readOptional_part [57, 48, 48, 49] record.fundingRateApplicable tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have fundingInterval := readOptional_part [57, 48, 48, 50] record.fundingInterval tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have fairValueLimit := readOptional_part [57, 48, 48, 51] record.fairValueLimit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have priorSettlPrice := readOptional_part [55, 51, 52] record.priorSettlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have settlPrice := readOptional_part [55, 51, 48] record.settlPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have settlPriceType := readOptional_part [55, 51, 49] record.settlPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have noUnderlyings := readOptional_part [55, 49, 49] record.noUnderlyings tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have underlyingSymbol := readOptional_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have noLegs := readGroup_part [53, 53, 53] [54, 48, 48] NoLegs.members NoLegs.encode NoLegs.within NoLegs.decode NoLegs.decode_encode NoLegs.led record.noLegs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  simp only [NoRelatedSymSecListGrp.decode, symbol, securityType, securitySubType, securityDesc, maturityMonthYear, putOrCall, strikePrice, asset, cFICode, underlyingProduct, mDSecurityTradingStatus, haltReason, currency, settlCurrency, minTradeVol, maxTradeVol, minPriceIncrement, largeTickThreshold, largeTick, noEvents, contractMultiplier, unitOfMeasure, unitOfMeasureQty, highLimitPrice, lowLimitPrice, maxPriceVariation, tradingReferenceDate, openInterestQty, clearedVolume, fundingRateApplicable, fundingInterval, fairValueLimit, priorSettlPrice, settlPrice, settlPriceType, noUnderlyings, underlyingSymbol, noLegs, some_bind] <;> rfl

theorem NoRelatedSymSecListGrp.taken (record : NoRelatedSymSecListGrp) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [55, 54, 50] record.securitySubType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [54, 57, 51, 55] record.asset (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [52, 54, 49] record.cFICode (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [52, 54, 50] record.underlyingProduct (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 54, 56, 50] record.mDSecurityTradingStatus (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [51, 50, 55] record.haltReason (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 50, 48] record.settlCurrency (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [53, 54, 50] record.minTradeVol (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [49, 49, 52, 48] record.maxTradeVol (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [57, 54, 57] record.minPriceIncrement (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 57, 48, 48, 49] record.largeTickThreshold (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 57, 48, 48, 50] record.largeTick (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_group pairing [56, 54, 52] NoEvents.members NoEvents.encode NoEvents.within (by decide) (by decide) NoEvents.taken record.noEvents)
                      (paired_cons pairing _ _ (paired_optional pairing [50, 51, 49] record.contractMultiplier (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [57, 57, 54] record.unitOfMeasure (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 55] record.unitOfMeasureQty (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 57] record.highLimitPrice (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 56] record.lowLimitPrice (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 52, 51] record.maxPriceVariation (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 54] record.tradingReferenceDate (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 50] record.openInterestQty (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [53, 55, 57, 49] record.clearedVolume (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 49] record.fundingRateApplicable (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 50] record.fundingInterval (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [57, 48, 48, 51] record.fairValueLimit (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [55, 51, 52] record.priorSettlPrice (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [55, 51, 48] record.settlPrice (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [55, 51, 49] record.settlPriceType (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [55, 49, 49] record.noUnderlyings (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_group pairing [53, 53, 53] NoLegs.members NoLegs.encode NoLegs.within (by decide) (by decide) NoLegs.taken record.noLegs)
                                        (paired_none pairing))))))))))))))))))))))))))))))))))))))

def NoRelatedSymSecListGrp.members : List (List UInt8) := NoRelatedSymSecListGrp.tags.flatten

def NoRelatedSymSecListGrp.encode (entry : NoRelatedSymSecListGrp) : List Token := encodeParts entry.parts

theorem NoRelatedSymSecListGrp.decode_encode (entry : NoRelatedSymSecListGrp) : NoRelatedSymSecListGrp.decode entry.encode = some entry :=
  NoRelatedSymSecListGrp.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSymSecListGrp.within (entry : NoRelatedSymSecListGrp) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSymSecListGrp.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSymSecListGrp.shape] at this

theorem NoRelatedSymSecListGrp.led (entry : NoRelatedSymSecListGrp) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSymSecListGrp.tags.tail rfl (by decide +kernel)

structure SecurityList where
  securityReqID : Terminated 1  -- tag 320
  securityResponseID : Terminated 1  -- tag 322
  securityRequestResult : Terminated 1  -- tag 560
  totNoRelatedSym : Option (Terminated 1)  -- tag 393
  lastFragment : Option (Terminated 1)  -- tag 893
  noRelatedSymSecListGrp : List NoRelatedSymSecListGrp  -- tag 146

def SecurityList.parts (record : SecurityList) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.required [51, 50, 50] record.securityResponseID,
   Part.required [53, 54, 48] record.securityRequestResult,
   Part.optional [51, 57, 51] record.totNoRelatedSym,
   Part.optional [56, 57, 51] record.lastFragment,
   Part.group [49, 52, 54] NoRelatedSymSecListGrp.members NoRelatedSymSecListGrp.encode NoRelatedSymSecListGrp.within record.noRelatedSymSecListGrp]

def SecurityList.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[51, 50, 50]], [[53, 54, 48]], [[51, 57, 51]], [[56, 57, 51]], [49, 52, 54] :: NoRelatedSymSecListGrp.members]

theorem SecurityList.shape (record : SecurityList) : record.parts.map Part.tags = SecurityList.tags := rfl

def SecurityList.decode (tokens : List Token) : Option SecurityList := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityResponseID ← readRequired [51, 50, 50] tokens
  let securityRequestResult ← readRequired [53, 54, 48] tokens
  let totNoRelatedSym ← readOptional [51, 57, 51] tokens
  let lastFragment ← readOptional [56, 57, 51] tokens
  let noRelatedSymSecListGrp ← readGroup [49, 52, 54] [53, 53] NoRelatedSymSecListGrp.members NoRelatedSymSecListGrp.decode tokens
  pure { securityReqID, securityResponseID, securityRequestResult, totNoRelatedSym, lastFragment, noRelatedSymSecListGrp }

theorem SecurityList.decode_agrees (record : SecurityList) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityList.decode tokens = some record := by
  have distinct : SecurityList.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityResponseID := readRequired_part [51, 50, 50] record.securityResponseID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityRequestResult := readRequired_part [53, 54, 48] record.securityRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have totNoRelatedSym := readOptional_part [51, 57, 51] record.totNoRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have lastFragment := readOptional_part [56, 57, 51] record.lastFragment tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noRelatedSymSecListGrp := readGroup_part [49, 52, 54] [53, 53] NoRelatedSymSecListGrp.members NoRelatedSymSecListGrp.encode NoRelatedSymSecListGrp.within NoRelatedSymSecListGrp.decode NoRelatedSymSecListGrp.decode_encode NoRelatedSymSecListGrp.led record.noRelatedSymSecListGrp tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [SecurityList.decode, securityReqID, securityResponseID, securityRequestResult, totNoRelatedSym, lastFragment, noRelatedSymSecListGrp, some_bind] <;> rfl

theorem SecurityList.taken (record : SecurityList) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 50, 50] record.securityResponseID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54, 48] record.securityRequestResult (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 57, 51] record.totNoRelatedSym (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [56, 57, 51] record.lastFragment (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSymSecListGrp.members NoRelatedSymSecListGrp.encode NoRelatedSymSecListGrp.within (by decide) (by decide) NoRelatedSymSecListGrp.taken record.noRelatedSymSecListGrp)
        (paired_none pairing))))))

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
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh)
  | marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject)
  | marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityDefinition (header : Header) (r0 : SecurityDefinition)
  | securityList (header : Header) (r0 : SecurityList)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataIncrementalRefresh header r0 => ⟨[51, 53], [88]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequestReject header r0 => ⟨[51, 53], [89]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataSnapshotFullRefresh header r0 => ⟨[51, 53], [87]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityDefinition header r0 => ⟨[51, 53], [100]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityList header r0 => ⟨[51, 53], [121]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value = [48] then
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
      else if token.value = [88] then
        if known (Header.tags ++ MarketDataIncrementalRefresh.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataIncrementalRefresh.decode rest
          pure (.marketDataIncrementalRefresh header r0)
        else none
      else if token.value = [89] then
        if known (Header.tags ++ MarketDataRequestReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataRequestReject.decode rest
          pure (.marketDataRequestReject header r0)
        else none
      else if token.value = [87] then
        if known (Header.tags ++ MarketDataSnapshotFullRefresh.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketDataSnapshotFullRefresh.decode rest
          pure (.marketDataSnapshotFullRefresh header r0)
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
      else if token.value = [100] then
        if known (Header.tags ++ SecurityDefinition.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityDefinition.decode rest
          pure (.securityDefinition header r0)
        else none
      else if token.value = [121] then
        if known (Header.tags ++ SecurityList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityList.decode rest
          pure (.securityList header r0)
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

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

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

theorem Message.decode_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decode (Message.tokens (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataIncrementalRefresh.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataIncrementalRefresh.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataIncrementalRefresh.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject) :
    Message.decode (Message.tokens (.marketDataRequestReject header r0)) = some (.marketDataRequestReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequestReject.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataRequestReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataRequestReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataRequestReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh) :
    Message.decode (Message.tokens (.marketDataSnapshotFullRefresh header r0)) = some (.marketDataSnapshotFullRefresh header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshotFullRefresh.tags) rfl rfl (by decide +kernel))
  have c1 := MarketDataSnapshotFullRefresh.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketDataSnapshotFullRefresh.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketDataSnapshotFullRefresh.tags) rfl
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

theorem Message.decode_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decode (Message.tokens (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityDefinition.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityDefinition.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityDefinition.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_securityList (header : Header) (r0 : SecurityList) :
    Message.decode (Message.tokens (.securityList header r0)) = some (.securityList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityList.tags) rfl
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
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decode_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decode_marketDataRequestReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decode_marketDataSnapshotFullRefresh header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityDefinition header r0 => exact Message.decode_securityDefinition header r0
  | securityList header r0 => exact Message.decode_securityList header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [106]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

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

theorem Message.decodeBytes_marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh) :
    Message.decodeBytes (Message.encode (.marketDataIncrementalRefresh header r0)) = some (.marketDataIncrementalRefresh header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [88]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataIncrementalRefresh.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataIncrementalRefresh header r0

theorem Message.decodeBytes_marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject) :
    Message.decodeBytes (Message.encode (.marketDataRequestReject header r0)) = some (.marketDataRequestReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [89]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataRequestReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataRequestReject header r0

theorem Message.decodeBytes_marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh) :
    Message.decodeBytes (Message.encode (.marketDataSnapshotFullRefresh header r0)) = some (.marketDataSnapshotFullRefresh header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [87]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketDataSnapshotFullRefresh.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketDataSnapshotFullRefresh header r0

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

theorem Message.decodeBytes_securityDefinition (header : Header) (r0 : SecurityDefinition) :
    Message.decodeBytes (Message.encode (.securityDefinition header r0)) = some (.securityDefinition header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [100]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityDefinition.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityDefinition header r0

theorem Message.decodeBytes_securityList (header : Header) (r0 : SecurityList) :
    Message.decodeBytes (Message.encode (.securityList header r0)) = some (.securityList header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [121]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityList.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityList header r0

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
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decodeBytes_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decodeBytes_marketDataRequestReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decodeBytes_marketDataSnapshotFullRefresh header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityDefinition header r0 => exact Message.decodeBytes_securityDefinition header r0
  | securityList header r0 => exact Message.decodeBytes_securityList header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseCoinbasederivativesMarketdataapiFixV027Exchange
