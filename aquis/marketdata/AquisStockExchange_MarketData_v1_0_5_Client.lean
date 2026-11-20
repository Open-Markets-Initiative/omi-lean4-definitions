import Wire

/-!
# Aquis Exchange  v1.0.5, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

Note: SignatureLength and Signature stand in the trailer ahead of CheckSum: read by tag wherever they stand, as every field of a body is, and written after the header's other fields.

License: MIT No Attribution
-/

namespace Omi.AquisAquisstockexchangeMarketdataFixV105Client

/-- Each Length tag counting a data field, and the field it counts -/
def pairing : Pairing :=
  [([57, 48], [57, 49]), ([57, 51], [56, 57]), ([50, 49, 50], [50, 49, 51])]

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
  noHops : Option (Terminated 1)  -- tag 627
  hopCompID : Option (Terminated 1)  -- tag 628
  hopSendingTime : Option (Terminated 1)  -- tag 629
  hopRefID : Option (Terminated 1)  -- tag 630
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
   Part.optional [54, 50, 55] record.noHops,
   Part.optional [54, 50, 56] record.hopCompID,
   Part.optional [54, 50, 57] record.hopSendingTime,
   Part.optional [54, 51, 48] record.hopRefID,
   Part.dataOptional [57, 51] [56, 57] record.signature]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[49, 49, 53]], [[49, 50, 56]], [[57, 48], [57, 49]], [[51, 52]], [[53, 48]], [[49, 52, 50]], [[53, 55]], [[49, 52, 51]], [[49, 49, 54]], [[49, 52, 52]], [[49, 50, 57]], [[49, 52, 53]], [[52, 51]], [[57, 55]], [[53, 50]], [[49, 50, 50]], [[50, 49, 50], [50, 49, 51]], [[51, 52, 55]], [[51, 54, 57]], [[54, 50, 55]], [[54, 50, 56]], [[54, 50, 57]], [[54, 51, 48]], [[57, 51], [56, 57]]]

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
  let noHops ← readOptional [54, 50, 55] tokens
  let hopCompID ← readOptional [54, 50, 56] tokens
  let hopSendingTime ← readOptional [54, 50, 57] tokens
  let hopRefID ← readOptional [54, 51, 48] tokens
  let signature ← readDataOptional [57, 51] [56, 57] tokens
  pure { senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, noHops, hopCompID, hopSendingTime, hopRefID, signature }

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
  have noHops := readOptional_part [54, 50, 55] record.noHops tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have hopCompID := readOptional_part [54, 50, 56] record.hopCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have hopSendingTime := readOptional_part [54, 50, 57] record.hopSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have hopRefID := readOptional_part [54, 51, 48] record.hopRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have signature := readDataOptional_part [57, 51] [56, 57] record.signature tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, onBehalfOfCompID, deliverToCompID, secureData, msgSeqNum, senderSubID, senderLocationID, targetSubID, targetLocationID, onBehalfOfSubID, onBehalfOfLocationID, deliverToSubID, deliverToLocationID, possDupFlag, possResend, sendingTime, origSendingTime, xmlData, messageEncoding, lastMsgSeqNumProcessed, noHops, hopCompID, hopSendingTime, hopRefID, signature, some_bind] <;> rfl

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
                       (paired_cons pairing _ _ (paired_optional pairing [54, 50, 55] record.noHops (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [54, 50, 56] record.hopCompID (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [54, 50, 57] record.hopSendingTime (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [54, 51, 48] record.hopRefID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_dataOptional pairing [57, 51] [56, 57] record.signature (by decide) (by decide))
                            (paired_none pairing))))))))))))))))))))))))))

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

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_none pairing))

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

structure NoMDEntryTypes where
  mDEntryType : Terminated 1  -- tag 269

def NoMDEntryTypes.parts (record : NoMDEntryTypes) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType]

def NoMDEntryTypes.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]]]

theorem NoMDEntryTypes.shape (record : NoMDEntryTypes) : record.parts.map Part.tags = NoMDEntryTypes.tags := rfl

def NoMDEntryTypes.decode (tokens : List Token) : Option NoMDEntryTypes := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  pure { mDEntryType }

theorem NoMDEntryTypes.decode_agrees (record : NoMDEntryTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntryTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntryTypes.decode tokens = some record := by
  have distinct : NoMDEntryTypes.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoMDEntryTypes.decode, mDEntryType, some_bind] <;> rfl

theorem NoMDEntryTypes.taken (record : NoMDEntryTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
   (paired_none pairing)

def NoMDEntryTypes.members : List (List UInt8) := NoMDEntryTypes.tags.flatten

def NoMDEntryTypes.encode (entry : NoMDEntryTypes) : List Token := encodeParts entry.parts

theorem NoMDEntryTypes.decode_encode (entry : NoMDEntryTypes) : NoMDEntryTypes.decode entry.encode = some entry :=
  NoMDEntryTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntryTypes.within (entry : NoMDEntryTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntryTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntryTypes.shape] at this

theorem NoMDEntryTypes.led (entry : NoMDEntryTypes) : Lead [50, 54, 57] entry.encode :=
  lead_parts [50, 54, 57] entry.mDEntryType _ NoMDEntryTypes.tags.tail rfl (by decide +kernel)

structure NoRelatedSym where
  tradingSessionID : Terminated 1  -- tag 336
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def NoRelatedSym.parts (record : NoRelatedSym) : List Part :=
  [Part.required [51, 51, 54] record.tradingSessionID,
   Part.optional [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def NoRelatedSym.tags : List (List (List UInt8)) :=
  [[[51, 51, 54]], [[53, 53]], [[52, 56]], [[50, 50]]]

theorem NoRelatedSym.shape (record : NoRelatedSym) : record.parts.map Part.tags = NoRelatedSym.tags := rfl

def NoRelatedSym.decode (tokens : List Token) : Option NoRelatedSym := do
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { tradingSessionID, symbol, securityID, securityIDSource }

theorem NoRelatedSym.decode_agrees (record : NoRelatedSym) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSym.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSym.decode tokens = some record := by
  have distinct : NoRelatedSym.tags.flatten.Nodup := by decide +kernel
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoRelatedSym.decode, tradingSessionID, symbol, securityID, securityIDSource, some_bind] <;> rfl

theorem NoRelatedSym.taken (record : NoRelatedSym) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
      (paired_none pairing))))

def NoRelatedSym.members : List (List UInt8) := NoRelatedSym.tags.flatten

def NoRelatedSym.encode (entry : NoRelatedSym) : List Token := encodeParts entry.parts

theorem NoRelatedSym.decode_encode (entry : NoRelatedSym) : NoRelatedSym.decode entry.encode = some entry :=
  NoRelatedSym.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSym.within (entry : NoRelatedSym) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSym.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSym.shape] at this

theorem NoRelatedSym.led (entry : NoRelatedSym) : Lead [51, 51, 54] entry.encode :=
  lead_parts [51, 51, 54] entry.tradingSessionID _ NoRelatedSym.tags.tail rfl (by decide +kernel)

structure MarketDataRequest where
  mDReqID : Terminated 1  -- tag 262
  subscriptionRequestType : Terminated 1  -- tag 263
  marketDepth : Terminated 1  -- tag 264
  noMDEntryTypes : List NoMDEntryTypes  -- tag 267
  noRelatedSym : List NoRelatedSym  -- tag 146

def MarketDataRequest.parts (record : MarketDataRequest) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [50, 54, 51] record.subscriptionRequestType,
   Part.required [50, 54, 52] record.marketDepth,
   Part.group [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within record.noMDEntryTypes,
   Part.group [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within record.noRelatedSym]

def MarketDataRequest.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 54, 51]], [[50, 54, 52]], [50, 54, 55] :: NoMDEntryTypes.members, [49, 52, 54] :: NoRelatedSym.members]

theorem MarketDataRequest.shape (record : MarketDataRequest) : record.parts.map Part.tags = MarketDataRequest.tags := rfl

def MarketDataRequest.decode (tokens : List Token) : Option MarketDataRequest := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let subscriptionRequestType ← readRequired [50, 54, 51] tokens
  let marketDepth ← readRequired [50, 54, 52] tokens
  let noMDEntryTypes ← readGroup [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.decode tokens
  let noRelatedSym ← readGroup [49, 52, 54] [51, 51, 54] NoRelatedSym.members NoRelatedSym.decode tokens
  pure { mDReqID, subscriptionRequestType, marketDepth, noMDEntryTypes, noRelatedSym }

theorem MarketDataRequest.decode_agrees (record : MarketDataRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequest.decode tokens = some record := by
  have distinct : MarketDataRequest.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have subscriptionRequestType := readRequired_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have marketDepth := readRequired_part [50, 54, 52] record.marketDepth tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noMDEntryTypes := readGroup_part [50, 54, 55] [50, 54, 57] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within NoMDEntryTypes.decode NoMDEntryTypes.decode_encode NoMDEntryTypes.led record.noMDEntryTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noRelatedSym := readGroup_part [49, 52, 54] [51, 51, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within NoRelatedSym.decode NoRelatedSym.decode_encode NoRelatedSym.led record.noRelatedSym tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [MarketDataRequest.decode, mDReqID, subscriptionRequestType, marketDepth, noMDEntryTypes, noRelatedSym, some_bind] <;> rfl

theorem MarketDataRequest.taken (record : MarketDataRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 54, 52] record.marketDepth (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [50, 54, 55] NoMDEntryTypes.members NoMDEntryTypes.encode NoMDEntryTypes.within (by decide) (by decide) NoMDEntryTypes.taken record.noMDEntryTypes)
      (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSym.members NoRelatedSym.encode NoRelatedSym.within (by decide) (by decide) NoRelatedSym.taken record.noRelatedSym)
       (paired_none pairing)))))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Option (Terminated 1)  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  text : Option (Terminated 1)  -- tag 58

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [51, 55, 49] record.refTagID,
   Part.optional [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [53, 56] record.text]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[53, 56]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readOptional [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { refSeqNum, refTagID, refMsgType, sessionRejectReason, text }

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
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, refTagID, refMsgType, sessionRejectReason, text, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
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

structure TradeCaptureReportRequest where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  text : Option (Terminated 1)  -- tag 58

def TradeCaptureReportRequest.parts (record : TradeCaptureReportRequest) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.optional [53, 56] record.text]

def TradeCaptureReportRequest.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[50, 54, 51]], [[53, 56]]]

theorem TradeCaptureReportRequest.shape (record : TradeCaptureReportRequest) : record.parts.map Part.tags = TradeCaptureReportRequest.tags := rfl

def TradeCaptureReportRequest.decode (tokens : List Token) : Option TradeCaptureReportRequest := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let text ← readOptional [53, 56] tokens
  pure { tradeRequestID, tradeRequestType, subscriptionRequestType, text }

theorem TradeCaptureReportRequest.decode_agrees (record : TradeCaptureReportRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequest.decode tokens = some record := by
  have distinct : TradeCaptureReportRequest.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [TradeCaptureReportRequest.decode, tradeRequestID, tradeRequestType, subscriptionRequestType, text, some_bind] <;> rfl

theorem TradeCaptureReportRequest.taken (record : TradeCaptureReportRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54, 57] record.tradeRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
      (paired_none pairing))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketDataRequest (header : Header) (r0 : MarketDataRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradeCaptureReportRequest (header : Header) (r0 : TradeCaptureReportRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequest header r0 => ⟨[51, 53], [86]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequest header r0 => ⟨[51, 53], [65, 68]⟩ :: encodeParts (header.parts ++ r0.parts)

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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDataRequest header r0 => exact Message.decode_marketDataRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decode_tradeCaptureReportRequest header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDataRequest header r0 => exact Message.decodeBytes_marketDataRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradeCaptureReportRequest header r0 => exact Message.decodeBytes_tradeCaptureReportRequest header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AquisAquisstockexchangeMarketdataFixV105Client
