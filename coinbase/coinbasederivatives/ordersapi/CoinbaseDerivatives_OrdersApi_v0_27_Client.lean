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

namespace Omi.CoinbaseCoinbasederivativesOrdersapiFixV027Client

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
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  xmlData : Option (List UInt8)  -- tag 213
  messageEncoding : Option (Terminated 1)  -- tag 347
  lastMsgSeqNumProcessed : Option (Terminated 1)  -- tag 369
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
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.dataOptional [50, 49, 50] [50, 49, 51] record.xmlData,
   Part.optional [51, 52, 55] record.messageEncoding,
   Part.optional [51, 54, 57] record.lastMsgSeqNumProcessed,
   Part.group [54, 50, 55] NoHops.members NoHops.encode NoHops.within record.noHops,
   Part.dataOptional [57, 51] [56, 57] record.signature]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[49, 49, 53]], [[49, 50, 56]], [[57, 48], [57, 49]], [[51, 52]], [[53, 48]], [[49, 52, 50]], [[53, 55]], [[49, 52, 51]], [[49, 49, 54]], [[49, 52, 52]], [[49, 50, 57]], [[49, 52, 53]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[50, 49, 50], [50, 49, 51]], [[51, 52, 55]], [[51, 54, 57]], [54, 50, 55] :: NoHops.members, [[57, 51], [56, 57]]]

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
  let noHops ← readGroup [54, 50, 55] [54, 50, 56] NoHops.members NoHops.decode tokens
  let signature ← readDataOptional [57, 51] [56, 57] tokens
  pure { senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, noHops, signature }

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
  have noHops := readGroup_part [54, 50, 55] [54, 50, 56] NoHops.members NoHops.encode NoHops.within NoHops.decode NoHops.decode_encode NoHops.led record.noHops tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have signature := readDataOptional_part [57, 51] [56, 57] record.signature tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, noHops, signature, some_bind] <;> rfl

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
                       (paired_cons pairing _ _ (paired_group pairing [54, 50, 55] NoHops.members NoHops.encode NoHops.within (by decide) (by decide) NoHops.taken record.noHops)
                        (paired_cons pairing _ _ (paired_dataOptional pairing [57, 51] [56, 57] record.signature (by decide) (by decide))
                         (paired_none pairing)))))))))))))))))))))))

structure ApplicationPing where
  pingId : Terminated 1  -- tag 22000
  requestTime : Option (Terminated 1)  -- tag 5979
  text : Option (Terminated 1)  -- tag 58

def ApplicationPing.parts (record : ApplicationPing) : List Part :=
  [Part.required [50, 50, 48, 48, 48] record.pingId,
   Part.optional [53, 57, 55, 57] record.requestTime,
   Part.optional [53, 56] record.text]

def ApplicationPing.tags : List (List (List UInt8)) :=
  [[[50, 50, 48, 48, 48]], [[53, 57, 55, 57]], [[53, 56]]]

theorem ApplicationPing.shape (record : ApplicationPing) : record.parts.map Part.tags = ApplicationPing.tags := rfl

def ApplicationPing.decode (tokens : List Token) : Option ApplicationPing := do
  let pingId ← readRequired [50, 50, 48, 48, 48] tokens
  let requestTime ← readOptional [53, 57, 55, 57] tokens
  let text ← readOptional [53, 56] tokens
  pure { pingId, requestTime, text }

theorem ApplicationPing.decode_agrees (record : ApplicationPing) (tokens : List Token)
    (agrees : ∀ tags ∈ ApplicationPing.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ApplicationPing.decode tokens = some record := by
  have distinct : ApplicationPing.tags.flatten.Nodup := by decide +kernel
  have pingId := readRequired_part [50, 50, 48, 48, 48] record.pingId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have requestTime := readOptional_part [53, 57, 55, 57] record.requestTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [ApplicationPing.decode, pingId, requestTime, text, some_bind] <;> rfl

theorem ApplicationPing.taken (record : ApplicationPing) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 50, 48, 48, 48] record.pingId (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 57, 55, 57] record.requestTime (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
     (paired_none pairing)))

structure EventResendRequest where
  beginExecId : Terminated 1  -- tag 22003
  endExecId : Option (Terminated 1)  -- tag 22004

def EventResendRequest.parts (record : EventResendRequest) : List Part :=
  [Part.required [50, 50, 48, 48, 51] record.beginExecId,
   Part.optional [50, 50, 48, 48, 52] record.endExecId]

def EventResendRequest.tags : List (List (List UInt8)) :=
  [[[50, 50, 48, 48, 51]], [[50, 50, 48, 48, 52]]]

theorem EventResendRequest.shape (record : EventResendRequest) : record.parts.map Part.tags = EventResendRequest.tags := rfl

def EventResendRequest.decode (tokens : List Token) : Option EventResendRequest := do
  let beginExecId ← readRequired [50, 50, 48, 48, 51] tokens
  let endExecId ← readOptional [50, 50, 48, 48, 52] tokens
  pure { beginExecId, endExecId }

theorem EventResendRequest.decode_agrees (record : EventResendRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ EventResendRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    EventResendRequest.decode tokens = some record := by
  have distinct : EventResendRequest.tags.flatten.Nodup := by decide +kernel
  have beginExecId := readRequired_part [50, 50, 48, 48, 51] record.beginExecId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have endExecId := readOptional_part [50, 50, 48, 48, 52] record.endExecId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [EventResendRequest.decode, beginExecId, endExecId, some_bind] <;> rfl

theorem EventResendRequest.taken (record : EventResendRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 50, 48, 48, 51] record.beginExecId (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 50, 48, 48, 52] record.endExecId (by decide) (by decide))
    (paired_none pairing))

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

structure LastExecIdRequest where
  testReqID : Option (Terminated 1)  -- tag 112

def LastExecIdRequest.parts (record : LastExecIdRequest) : List Part :=
  [Part.optional [49, 49, 50] record.testReqID]

def LastExecIdRequest.tags : List (List (List UInt8)) :=
  [[[49, 49, 50]]]

theorem LastExecIdRequest.shape (record : LastExecIdRequest) : record.parts.map Part.tags = LastExecIdRequest.tags := rfl

def LastExecIdRequest.decode (tokens : List Token) : Option LastExecIdRequest := do
  let testReqID ← readOptional [49, 49, 50] tokens
  pure { testReqID }

theorem LastExecIdRequest.decode_agrees (record : LastExecIdRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ LastExecIdRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    LastExecIdRequest.decode tokens = some record := by
  have distinct : LastExecIdRequest.tags.flatten.Nodup := by decide +kernel
  have testReqID := readOptional_part [49, 49, 50] record.testReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [LastExecIdRequest.decode, testReqID, some_bind] <;> rfl

theorem LastExecIdRequest.taken (record : LastExecIdRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 49, 50] record.testReqID (by decide) (by decide))
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

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 53, 50] record.partyRole (by decide) (by decide))
     (paired_none pairing)))

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
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  securityDesc : Option (Terminated 1)  -- tag 107
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  positionEffect : Option (Terminated 1)  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  orderCapacity : Terminated 1  -- tag 528
  maxShow : Option (Terminated 1)  -- tag 210
  expireDate : Option (Terminated 1)  -- tag 432
  manualOrderIndicator : Terminated 1  -- tag 1028
  custOrderHandlingInst : Terminated 1  -- tag 1031
  selfMatchPreventionId : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 8000
  custOrderCapacity : Terminated 1  -- tag 582
  execInst : Option (Terminated 1)  -- tag 18
  stopLimitPx : Option (Terminated 1)  -- tag 3040

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 55] record.positionEffect,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.required [49, 48, 51, 49] record.custOrderHandlingInst,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionId,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionInstruction,
   Part.required [53, 56, 50] record.custOrderCapacity,
   Part.optional [49, 56] record.execInst,
   Part.optional [51, 48, 52, 48] record.stopLimitPx]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[49, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[49, 48, 55]], [[50, 48, 49]], [[50, 48, 50]], [[53, 57]], [[54, 48]], [[55, 55]], [[57, 57]], [[49, 49, 48]], [[53, 50, 56]], [[50, 49, 48]], [[52, 51, 50]], [[49, 48, 50, 56]], [[49, 48, 51, 49]], [[55, 57, 50, 56]], [[56, 48, 48, 48]], [[53, 56, 50]], [[49, 56]], [[51, 48, 52, 48]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let custOrderHandlingInst ← readRequired [49, 48, 51, 49] tokens
  let selfMatchPreventionId ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionInstruction ← readOptional [56, 48, 48, 48] tokens
  let custOrderCapacity ← readRequired [53, 56, 50] tokens
  let execInst ← readOptional [49, 56] tokens
  let stopLimitPx ← readOptional [51, 48, 52, 48] tokens
  pure { noPartyIDs, account, clOrdID, orderQty, ordType, price, side, symbol, securityType, securityDesc, putOrCall, strikePrice, timeInForce, transactTime, positionEffect, stopPx, minQty, orderCapacity, maxShow, expireDate, manualOrderIndicator, custOrderHandlingInst, selfMatchPreventionId, selfMatchPreventionInstruction, custOrderCapacity, execInst, stopLimitPx }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have custOrderHandlingInst := readRequired_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have selfMatchPreventionId := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have custOrderCapacity := readRequired_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have stopLimitPx := readOptional_part [51, 48, 52, 48] record.stopLimitPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  simp only [NewOrderSingle.decode, noPartyIDs, account, clOrdID, orderQty, ordType, price, side, symbol, securityType, securityDesc, putOrCall, strikePrice, timeInForce, transactTime, positionEffect, stopPx, minQty, orderCapacity, maxShow, expireDate, manualOrderIndicator, custOrderHandlingInst, selfMatchPreventionId, selfMatchPreventionInstruction, custOrderCapacity, execInst, stopLimitPx, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.positionEffect (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [49, 48, 51, 49] record.custOrderHandlingInst (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionId (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionInstruction (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [53, 56, 50] record.custOrderCapacity (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [51, 48, 52, 48] record.stopLimitPx (by decide) (by decide))
                             (paired_none pairing)))))))))))))))))))))))))))

structure OrderCancelReplaceRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  securityDesc : Option (Terminated 1)  -- tag 107
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  positionEffect : Option (Terminated 1)  -- tag 77
  stopPx : Option (Terminated 1)  -- tag 99
  minQty : Option (Terminated 1)  -- tag 110
  orderCapacity : Terminated 1  -- tag 528
  maxShow : Option (Terminated 1)  -- tag 210
  expireDate : Option (Terminated 1)  -- tag 432
  manualOrderIndicator : Terminated 1  -- tag 1028
  custOrderHandlingInst : Terminated 1  -- tag 1031
  selfMatchPreventionId : Option (Terminated 1)  -- tag 7928
  selfMatchPreventionInstruction : Option (Terminated 1)  -- tag 8000
  custOrderCapacity : Terminated 1  -- tag 582
  stopLimitPx : Option (Terminated 1)  -- tag 3040

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [55, 55] record.positionEffect,
   Part.optional [57, 57] record.stopPx,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [53, 50, 56] record.orderCapacity,
   Part.optional [50, 49, 48] record.maxShow,
   Part.optional [52, 51, 50] record.expireDate,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator,
   Part.required [49, 48, 51, 49] record.custOrderHandlingInst,
   Part.optional [55, 57, 50, 56] record.selfMatchPreventionId,
   Part.optional [56, 48, 48, 48] record.selfMatchPreventionInstruction,
   Part.required [53, 56, 50] record.custOrderCapacity,
   Part.optional [51, 48, 52, 48] record.stopLimitPx]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[49, 49]], [[51, 55]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[49, 48, 55]], [[50, 48, 49]], [[50, 48, 50]], [[53, 57]], [[54, 48]], [[55, 55]], [[57, 57]], [[49, 49, 48]], [[53, 50, 56]], [[50, 49, 48]], [[52, 51, 50]], [[49, 48, 50, 56]], [[49, 48, 51, 49]], [[55, 57, 50, 56]], [[56, 48, 48, 48]], [[53, 56, 50]], [[51, 48, 52, 48]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let positionEffect ← readOptional [55, 55] tokens
  let stopPx ← readOptional [57, 57] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let orderCapacity ← readRequired [53, 50, 56] tokens
  let maxShow ← readOptional [50, 49, 48] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  let custOrderHandlingInst ← readRequired [49, 48, 51, 49] tokens
  let selfMatchPreventionId ← readOptional [55, 57, 50, 56] tokens
  let selfMatchPreventionInstruction ← readOptional [56, 48, 48, 48] tokens
  let custOrderCapacity ← readRequired [53, 56, 50] tokens
  let stopLimitPx ← readOptional [51, 48, 52, 48] tokens
  pure { noPartyIDs, account, clOrdID, orderID, orderQty, ordType, origClOrdID, price, side, symbol, securityType, securityDesc, putOrCall, strikePrice, timeInForce, transactTime, positionEffect, stopPx, minQty, orderCapacity, maxShow, expireDate, manualOrderIndicator, custOrderHandlingInst, selfMatchPreventionId, selfMatchPreventionInstruction, custOrderCapacity, stopLimitPx }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have positionEffect := readOptional_part [55, 55] record.positionEffect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have orderCapacity := readRequired_part [53, 50, 56] record.orderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maxShow := readOptional_part [50, 49, 48] record.maxShow tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have custOrderHandlingInst := readRequired_part [49, 48, 51, 49] record.custOrderHandlingInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have selfMatchPreventionId := readOptional_part [55, 57, 50, 56] record.selfMatchPreventionId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have selfMatchPreventionInstruction := readOptional_part [56, 48, 48, 48] record.selfMatchPreventionInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have custOrderCapacity := readRequired_part [53, 56, 50] record.custOrderCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have stopLimitPx := readOptional_part [51, 48, 52, 48] record.stopLimitPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, noPartyIDs, account, clOrdID, orderID, orderQty, ordType, origClOrdID, price, side, symbol, securityType, securityDesc, putOrCall, strikePrice, timeInForce, transactTime, positionEffect, stopPx, minQty, orderCapacity, maxShow, expireDate, manualOrderIndicator, custOrderHandlingInst, selfMatchPreventionId, selfMatchPreventionInstruction, custOrderCapacity, stopLimitPx, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [55, 55] record.positionEffect (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [53, 50, 56] record.orderCapacity (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 48] record.maxShow (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [49, 48, 51, 49] record.custOrderHandlingInst (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [55, 57, 50, 56] record.selfMatchPreventionId (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [56, 48, 48, 48] record.selfMatchPreventionInstruction (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_required pairing [53, 56, 50] record.custOrderCapacity (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [51, 48, 52, 48] record.stopLimitPx (by decide) (by decide))
                              (paired_none pairing))))))))))))))))))))))))))))

structure OrderCancelRequest where
  noPartyIDs : List NoPartyIDs  -- tag 453
  account : Terminated 1  -- tag 1
  clOrdID : Terminated 1  -- tag 11
  orderID : Terminated 1  -- tag 37
  origClOrdID : Option (Terminated 1)  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  securityType : Terminated 1  -- tag 167
  securityDesc : Option (Terminated 1)  -- tag 107
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  transactTime : Terminated 1  -- tag 60
  manualOrderIndicator : Terminated 1  -- tag 1028

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [49] record.account,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 55] record.orderID,
   Part.optional [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [49, 54, 55] record.securityType,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[49]], [[49, 49]], [[51, 55]], [[52, 49]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[49, 48, 55]], [[50, 48, 49]], [[50, 48, 50]], [[54, 48]], [[49, 48, 50, 56]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let account ← readRequired [49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readRequired [51, 55] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityType ← readRequired [49, 54, 55] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let transactTime ← readRequired [54, 48] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  pure { noPartyIDs, account, clOrdID, orderID, origClOrdID, side, symbol, securityType, securityDesc, putOrCall, strikePrice, transactTime, manualOrderIndicator }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have account := readRequired_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityType := readRequired_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, noPartyIDs, account, clOrdID, orderID, origClOrdID, side, symbol, securityType, securityDesc, putOrCall, strikePrice, transactTime, manualOrderIndicator, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_required pairing [49] record.account (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [49, 54, 55] record.securityType (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure OrderMassCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  massCancelRequestType : Terminated 1  -- tag 530
  tradingSessionID : Option (Terminated 1)  -- tag 336
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  symbol : Option (Terminated 1)  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  securityDesc : Option (Terminated 1)  -- tag 107
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  side : Option (Terminated 1)  -- tag 54
  transactTime : Terminated 1  -- tag 60
  text : Option (Terminated 1)  -- tag 58
  encodedText : Option (List UInt8)  -- tag 355

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [53, 51, 48] record.massCancelRequestType,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.optional [53, 52] record.side,
   Part.required [54, 48] record.transactTime,
   Part.optional [53, 56] record.text,
   Part.dataOptional [51, 53, 52] [51, 53, 53] record.encodedText]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[53, 51, 48]], [[51, 51, 54]], [[54, 50, 53]], [[53, 53]], [[49, 54, 55]], [[49, 48, 55]], [[50, 48, 49]], [[50, 48, 50]], [[53, 52]], [[54, 48]], [[53, 56]], [[51, 53, 52], [51, 53, 53]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let massCancelRequestType ← readRequired [53, 51, 48] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let side ← readOptional [53, 52] tokens
  let transactTime ← readRequired [54, 48] tokens
  let text ← readOptional [53, 56] tokens
  let encodedText ← readDataOptional [51, 53, 52] [51, 53, 53] tokens
  pure { clOrdID, massCancelRequestType, tradingSessionID, tradingSessionSubID, symbol, securityType, securityDesc, putOrCall, strikePrice, side, transactTime, text, encodedText }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have massCancelRequestType := readRequired_part [53, 51, 48] record.massCancelRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have encodedText := readDataOptional_part [51, 53, 52] [51, 53, 53] record.encodedText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, clOrdID, massCancelRequestType, tradingSessionID, tradingSessionSubID, symbol, securityType, securityDesc, putOrCall, strikePrice, side, transactTime, text, encodedText, some_bind] <;> rfl

theorem OrderMassCancelRequest.taken (record : OrderMassCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.massCancelRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [54, 50, 53] record.tradingSessionSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
              (paired_cons pairing _ _ (paired_dataOptional pairing [51, 53, 52] [51, 53, 53] record.encodedText (by decide) (by decide))
               (paired_none pairing)))))))))))))

structure OrderStatusRequest where
  clOrdID : Terminated 1  -- tag 11
  orderID : Option (Terminated 1)  -- tag 37
  side : Terminated 1  -- tag 54
  symbol : Option (Terminated 1)  -- tag 55
  securityType : Option (Terminated 1)  -- tag 167
  securityDesc : Option (Terminated 1)  -- tag 107
  putOrCall : Option (Terminated 1)  -- tag 201
  strikePrice : Option (Terminated 1)  -- tag 202
  transactTime : Terminated 1  -- tag 60
  manualOrderIndicator : Terminated 1  -- tag 1028

def OrderStatusRequest.parts (record : OrderStatusRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [51, 55] record.orderID,
   Part.required [53, 52] record.side,
   Part.optional [53, 53] record.symbol,
   Part.optional [49, 54, 55] record.securityType,
   Part.optional [49, 48, 55] record.securityDesc,
   Part.optional [50, 48, 49] record.putOrCall,
   Part.optional [50, 48, 50] record.strikePrice,
   Part.required [54, 48] record.transactTime,
   Part.required [49, 48, 50, 56] record.manualOrderIndicator]

def OrderStatusRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 55]], [[53, 52]], [[53, 53]], [[49, 54, 55]], [[49, 48, 55]], [[50, 48, 49]], [[50, 48, 50]], [[54, 48]], [[49, 48, 50, 56]]]

theorem OrderStatusRequest.shape (record : OrderStatusRequest) : record.parts.map Part.tags = OrderStatusRequest.tags := rfl

def OrderStatusRequest.decode (tokens : List Token) : Option OrderStatusRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderID ← readOptional [51, 55] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let securityDesc ← readOptional [49, 48, 55] tokens
  let putOrCall ← readOptional [50, 48, 49] tokens
  let strikePrice ← readOptional [50, 48, 50] tokens
  let transactTime ← readRequired [54, 48] tokens
  let manualOrderIndicator ← readRequired [49, 48, 50, 56] tokens
  pure { clOrdID, orderID, side, symbol, securityType, securityDesc, putOrCall, strikePrice, transactTime, manualOrderIndicator }

theorem OrderStatusRequest.decode_agrees (record : OrderStatusRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderStatusRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderStatusRequest.decode tokens = some record := by
  have distinct : OrderStatusRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have securityDesc := readOptional_part [49, 48, 55] record.securityDesc tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have putOrCall := readOptional_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have strikePrice := readOptional_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have manualOrderIndicator := readRequired_part [49, 48, 50, 56] record.manualOrderIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  simp only [OrderStatusRequest.decode, clOrdID, orderID, side, symbol, securityType, securityDesc, putOrCall, strikePrice, transactTime, manualOrderIndicator, some_bind] <;> rfl

theorem OrderStatusRequest.taken (record : OrderStatusRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55] record.securityDesc (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [49, 48, 50, 56] record.manualOrderIndicator (by decide) (by decide))
            (paired_none pairing))))))))))

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
  | applicationPing (header : Header) (r0 : ApplicationPing)
  | eventResendRequest (header : Header) (r0 : EventResendRequest)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | lastExecIdRequest (header : Header) (r0 : LastExecIdRequest)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | orderStatusRequest (header : Header) (r0 : OrderStatusRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .applicationPing header r0 => ⟨[51, 53], [70, 65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .eventResendRequest header r0 => ⟨[51, 53], [70, 51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .lastExecIdRequest header r0 => ⟨[51, 53], [70, 49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], [113]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderStatusRequest header r0 => ⟨[51, 53], [72]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [70, 65] then
        if known (Header.tags ++ ApplicationPing.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ApplicationPing.decode rest
          pure (.applicationPing header r0)
        else none
      else if token.value = [70, 51] then
        if known (Header.tags ++ EventResendRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← EventResendRequest.decode rest
          pure (.eventResendRequest header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else if token.value = [70, 49] then
        if known (Header.tags ++ LastExecIdRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← LastExecIdRequest.decode rest
          pure (.lastExecIdRequest header r0)
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
      else if token.value = [72] then
        if known (Header.tags ++ OrderStatusRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderStatusRequest.decode rest
          pure (.orderStatusRequest header r0)
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

theorem Message.decode_applicationPing (header : Header) (r0 : ApplicationPing) :
    Message.decode (Message.tokens (.applicationPing header r0)) = some (.applicationPing header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationPing.tags) rfl rfl (by decide +kernel))
  have c1 := ApplicationPing.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ApplicationPing.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ApplicationPing.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_eventResendRequest (header : Header) (r0 : EventResendRequest) :
    Message.decode (Message.tokens (.eventResendRequest header r0)) = some (.eventResendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (EventResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := EventResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (EventResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ EventResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_lastExecIdRequest (header : Header) (r0 : LastExecIdRequest) :
    Message.decode (Message.tokens (.lastExecIdRequest header r0)) = some (.lastExecIdRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (LastExecIdRequest.tags) rfl rfl (by decide +kernel))
  have c1 := LastExecIdRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (LastExecIdRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ LastExecIdRequest.tags) rfl
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

theorem Message.decode_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decode (Message.tokens (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderStatusRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderStatusRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderStatusRequest.tags) rfl
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
  | applicationPing header r0 => exact Message.decode_applicationPing header r0
  | eventResendRequest header r0 => exact Message.decode_eventResendRequest header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | lastExecIdRequest header r0 => exact Message.decode_lastExecIdRequest header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
  | orderStatusRequest header r0 => exact Message.decode_orderStatusRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_applicationPing (header : Header) (r0 : ApplicationPing) :
    Message.decodeBytes (Message.encode (.applicationPing header r0)) = some (.applicationPing header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ApplicationPing.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_applicationPing header r0

theorem Message.decodeBytes_eventResendRequest (header : Header) (r0 : EventResendRequest) :
    Message.decodeBytes (Message.encode (.eventResendRequest header r0)) = some (.eventResendRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 51]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (EventResendRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_eventResendRequest header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_lastExecIdRequest (header : Header) (r0 : LastExecIdRequest) :
    Message.decodeBytes (Message.encode (.lastExecIdRequest header r0)) = some (.lastExecIdRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70, 49]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (LastExecIdRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_lastExecIdRequest header r0

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

theorem Message.decodeBytes_orderStatusRequest (header : Header) (r0 : OrderStatusRequest) :
    Message.decodeBytes (Message.encode (.orderStatusRequest header r0)) = some (.orderStatusRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [72]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderStatusRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderStatusRequest header r0

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
  | applicationPing header r0 => exact Message.decodeBytes_applicationPing header r0
  | eventResendRequest header r0 => exact Message.decodeBytes_eventResendRequest header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | lastExecIdRequest header r0 => exact Message.decodeBytes_lastExecIdRequest header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | orderStatusRequest header r0 => exact Message.decodeBytes_orderStatusRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CoinbaseCoinbasederivativesOrdersapiFixV027Client
