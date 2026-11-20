import Wire

/-!
# Aquis Exchange  v1.0.5, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

Note: SignatureLength and Signature stand in the trailer ahead of CheckSum: read by tag wherever they stand, as every field of a body is, and written after the header's other fields.

License: MIT No Attribution
-/

namespace Omi.AquisAquisstockexchangeMarketdataFixV105Exchange

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

structure NoMDEntriesIncremental where
  mDUpdateAction : Terminated 1  -- tag 279
  mDEntryType : Option (Terminated 1)  -- tag 269
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryOriginator : Option (Terminated 1)  -- tag 282
  symbol : Terminated 1  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  tradingSessionID : Terminated 1  -- tag 336

def NoMDEntriesIncremental.parts (record : NoMDEntriesIncremental) : List Part :=
  [Part.required [50, 55, 57] record.mDUpdateAction,
   Part.optional [50, 54, 57] record.mDEntryType,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 56, 50] record.mDEntryOriginator,
   Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [51, 51, 54] record.tradingSessionID]

def NoMDEntriesIncremental.tags : List (List (List UInt8)) :=
  [[[50, 55, 57]], [[50, 54, 57]], [[50, 55, 48]], [[50, 55, 49]], [[50, 56, 50]], [[53, 53]], [[52, 56]], [[50, 50]], [[51, 51, 54]]]

theorem NoMDEntriesIncremental.shape (record : NoMDEntriesIncremental) : record.parts.map Part.tags = NoMDEntriesIncremental.tags := rfl

def NoMDEntriesIncremental.decode (tokens : List Token) : Option NoMDEntriesIncremental := do
  let mDUpdateAction ← readRequired [50, 55, 57] tokens
  let mDEntryType ← readOptional [50, 54, 57] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryOriginator ← readOptional [50, 56, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { mDUpdateAction, mDEntryType, mDEntryPx, mDEntrySize, mDEntryOriginator, symbol, securityID, securityIDSource, tradingSessionID }

theorem NoMDEntriesIncremental.decode_agrees (record : NoMDEntriesIncremental) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntriesIncremental.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntriesIncremental.decode tokens = some record := by
  have distinct : NoMDEntriesIncremental.tags.flatten.Nodup := by decide +kernel
  have mDUpdateAction := readRequired_part [50, 55, 57] record.mDUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryType := readOptional_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have mDEntryOriginator := readOptional_part [50, 56, 50] record.mDEntryOriginator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [NoMDEntriesIncremental.decode, mDUpdateAction, mDEntryType, mDEntryPx, mDEntrySize, mDEntryOriginator, symbol, securityID, securityIDSource, tradingSessionID, some_bind] <;> rfl

theorem NoMDEntriesIncremental.taken (record : NoMDEntriesIncremental) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 55, 57] record.mDUpdateAction (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48] record.mDEntryPx (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 55, 49] record.mDEntrySize (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 56, 50] record.mDEntryOriginator (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 56] record.securityID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 50] record.securityIDSource (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
           (paired_none pairing)))))))))

def NoMDEntriesIncremental.members : List (List UInt8) := NoMDEntriesIncremental.tags.flatten

def NoMDEntriesIncremental.encode (entry : NoMDEntriesIncremental) : List Token := encodeParts entry.parts

theorem NoMDEntriesIncremental.decode_encode (entry : NoMDEntriesIncremental) : NoMDEntriesIncremental.decode entry.encode = some entry :=
  NoMDEntriesIncremental.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMDEntriesIncremental.within (entry : NoMDEntriesIncremental) : ∀ token ∈ entry.encode, token.tag ∈ NoMDEntriesIncremental.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMDEntriesIncremental.shape] at this

theorem NoMDEntriesIncremental.led (entry : NoMDEntriesIncremental) : Lead [50, 55, 57] entry.encode :=
  lead_parts [50, 55, 57] entry.mDUpdateAction _ NoMDEntriesIncremental.tags.tail rfl (by decide +kernel)

structure MarketDataIncrementalRefresh where
  mDReqID : Terminated 1  -- tag 262
  noMDEntriesIncremental : List NoMDEntriesIncremental  -- tag 268

def MarketDataIncrementalRefresh.parts (record : MarketDataIncrementalRefresh) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.group [50, 54, 56] NoMDEntriesIncremental.members NoMDEntriesIncremental.encode NoMDEntriesIncremental.within record.noMDEntriesIncremental]

def MarketDataIncrementalRefresh.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [50, 54, 56] :: NoMDEntriesIncremental.members]

theorem MarketDataIncrementalRefresh.shape (record : MarketDataIncrementalRefresh) : record.parts.map Part.tags = MarketDataIncrementalRefresh.tags := rfl

def MarketDataIncrementalRefresh.decode (tokens : List Token) : Option MarketDataIncrementalRefresh := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let noMDEntriesIncremental ← readGroup [50, 54, 56] [50, 55, 57] NoMDEntriesIncremental.members NoMDEntriesIncremental.decode tokens
  pure { mDReqID, noMDEntriesIncremental }

theorem MarketDataIncrementalRefresh.decode_agrees (record : MarketDataIncrementalRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataIncrementalRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataIncrementalRefresh.decode tokens = some record := by
  have distinct : MarketDataIncrementalRefresh.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noMDEntriesIncremental := readGroup_part [50, 54, 56] [50, 55, 57] NoMDEntriesIncremental.members NoMDEntriesIncremental.encode NoMDEntriesIncremental.within NoMDEntriesIncremental.decode NoMDEntriesIncremental.decode_encode NoMDEntriesIncremental.led record.noMDEntriesIncremental tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [MarketDataIncrementalRefresh.decode, mDReqID, noMDEntriesIncremental, some_bind] <;> rfl

theorem MarketDataIncrementalRefresh.taken (record : MarketDataIncrementalRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntriesIncremental.members NoMDEntriesIncremental.encode NoMDEntriesIncremental.within (by decide) (by decide) NoMDEntriesIncremental.taken record.noMDEntriesIncremental)
    (paired_none pairing))

structure MarketDataRequestReject where
  mDReqID : Terminated 1  -- tag 262
  mDReqRejReason : Option (Terminated 1)  -- tag 281

def MarketDataRequestReject.parts (record : MarketDataRequestReject) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.optional [50, 56, 49] record.mDReqRejReason]

def MarketDataRequestReject.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[50, 56, 49]]]

theorem MarketDataRequestReject.shape (record : MarketDataRequestReject) : record.parts.map Part.tags = MarketDataRequestReject.tags := rfl

def MarketDataRequestReject.decode (tokens : List Token) : Option MarketDataRequestReject := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let mDReqRejReason ← readOptional [50, 56, 49] tokens
  pure { mDReqID, mDReqRejReason }

theorem MarketDataRequestReject.decode_agrees (record : MarketDataRequestReject) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataRequestReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataRequestReject.decode tokens = some record := by
  have distinct : MarketDataRequestReject.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDReqRejReason := readOptional_part [50, 56, 49] record.mDReqRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [MarketDataRequestReject.decode, mDReqID, mDReqRejReason, some_bind] <;> rfl

theorem MarketDataRequestReject.taken (record : MarketDataRequestReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 56, 49] record.mDReqRejReason (by decide) (by decide))
    (paired_none pairing))

structure NoMDEntries where
  mDEntryType : Terminated 1  -- tag 269
  mDEntryPx : Option (Terminated 1)  -- tag 270
  mDEntrySize : Option (Terminated 1)  -- tag 271
  mDEntryOriginator : Option (Terminated 1)  -- tag 282

def NoMDEntries.parts (record : NoMDEntries) : List Part :=
  [Part.required [50, 54, 57] record.mDEntryType,
   Part.optional [50, 55, 48] record.mDEntryPx,
   Part.optional [50, 55, 49] record.mDEntrySize,
   Part.optional [50, 56, 50] record.mDEntryOriginator]

def NoMDEntries.tags : List (List (List UInt8)) :=
  [[[50, 54, 57]], [[50, 55, 48]], [[50, 55, 49]], [[50, 56, 50]]]

theorem NoMDEntries.shape (record : NoMDEntries) : record.parts.map Part.tags = NoMDEntries.tags := rfl

def NoMDEntries.decode (tokens : List Token) : Option NoMDEntries := do
  let mDEntryType ← readRequired [50, 54, 57] tokens
  let mDEntryPx ← readOptional [50, 55, 48] tokens
  let mDEntrySize ← readOptional [50, 55, 49] tokens
  let mDEntryOriginator ← readOptional [50, 56, 50] tokens
  pure { mDEntryType, mDEntryPx, mDEntrySize, mDEntryOriginator }

theorem NoMDEntries.decode_agrees (record : NoMDEntries) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMDEntries.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMDEntries.decode tokens = some record := by
  have distinct : NoMDEntries.tags.flatten.Nodup := by decide +kernel
  have mDEntryType := readRequired_part [50, 54, 57] record.mDEntryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have mDEntryPx := readOptional_part [50, 55, 48] record.mDEntryPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have mDEntrySize := readOptional_part [50, 55, 49] record.mDEntrySize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have mDEntryOriginator := readOptional_part [50, 56, 50] record.mDEntryOriginator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoMDEntries.decode, mDEntryType, mDEntryPx, mDEntrySize, mDEntryOriginator, some_bind] <;> rfl

theorem NoMDEntries.taken (record : NoMDEntries) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 57] record.mDEntryType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48] record.mDEntryPx (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 55, 49] record.mDEntrySize (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 56, 50] record.mDEntryOriginator (by decide) (by decide))
      (paired_none pairing))))

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
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  tradingSessionID : Terminated 1  -- tag 336
  noMDEntries : List NoMDEntries  -- tag 268

def MarketDataSnapshotFullRefresh.parts (record : MarketDataSnapshotFullRefresh) : List Part :=
  [Part.required [50, 54, 50] record.mDReqID,
   Part.required [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [51, 51, 54] record.tradingSessionID,
   Part.group [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within record.noMDEntries]

def MarketDataSnapshotFullRefresh.tags : List (List (List UInt8)) :=
  [[[50, 54, 50]], [[53, 53]], [[52, 56]], [[50, 50]], [[51, 51, 54]], [50, 54, 56] :: NoMDEntries.members]

theorem MarketDataSnapshotFullRefresh.shape (record : MarketDataSnapshotFullRefresh) : record.parts.map Part.tags = MarketDataSnapshotFullRefresh.tags := rfl

def MarketDataSnapshotFullRefresh.decode (tokens : List Token) : Option MarketDataSnapshotFullRefresh := do
  let mDReqID ← readRequired [50, 54, 50] tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let noMDEntries ← readGroup [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.decode tokens
  pure { mDReqID, symbol, securityID, securityIDSource, tradingSessionID, noMDEntries }

theorem MarketDataSnapshotFullRefresh.decode_agrees (record : MarketDataSnapshotFullRefresh) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketDataSnapshotFullRefresh.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketDataSnapshotFullRefresh.decode tokens = some record := by
  have distinct : MarketDataSnapshotFullRefresh.tags.flatten.Nodup := by decide +kernel
  have mDReqID := readRequired_part [50, 54, 50] record.mDReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have noMDEntries := readGroup_part [50, 54, 56] [50, 54, 57] NoMDEntries.members NoMDEntries.encode NoMDEntries.within NoMDEntries.decode NoMDEntries.decode_encode NoMDEntries.led record.noMDEntries tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [MarketDataSnapshotFullRefresh.decode, mDReqID, symbol, securityID, securityIDSource, tradingSessionID, noMDEntries, some_bind] <;> rfl

theorem MarketDataSnapshotFullRefresh.taken (record : MarketDataSnapshotFullRefresh) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 54, 50] record.mDReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 56] record.securityID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [50, 50] record.securityIDSource (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_group pairing [50, 54, 56] NoMDEntries.members NoMDEntries.encode NoMDEntries.within (by decide) (by decide) NoMDEntries.taken record.noMDEntries)
        (paired_none pairing))))))

structure NoRelatedSymNews where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22

def NoRelatedSymNews.parts (record : NoRelatedSymNews) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource]

def NoRelatedSymNews.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]]]

theorem NoRelatedSymNews.shape (record : NoRelatedSymNews) : record.parts.map Part.tags = NoRelatedSymNews.tags := rfl

def NoRelatedSymNews.decode (tokens : List Token) : Option NoRelatedSymNews := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  pure { symbol, securityID, securityIDSource }

theorem NoRelatedSymNews.decode_agrees (record : NoRelatedSymNews) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRelatedSymNews.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRelatedSymNews.decode tokens = some record := by
  have distinct : NoRelatedSymNews.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRelatedSymNews.decode, symbol, securityID, securityIDSource, some_bind] <;> rfl

theorem NoRelatedSymNews.taken (record : NoRelatedSymNews) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
     (paired_none pairing)))

def NoRelatedSymNews.members : List (List UInt8) := NoRelatedSymNews.tags.flatten

def NoRelatedSymNews.encode (entry : NoRelatedSymNews) : List Token := encodeParts entry.parts

theorem NoRelatedSymNews.decode_encode (entry : NoRelatedSymNews) : NoRelatedSymNews.decode entry.encode = some entry :=
  NoRelatedSymNews.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRelatedSymNews.within (entry : NoRelatedSymNews) : ∀ token ∈ entry.encode, token.tag ∈ NoRelatedSymNews.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRelatedSymNews.shape] at this

theorem NoRelatedSymNews.led (entry : NoRelatedSymNews) : Lead [53, 53] entry.encode :=
  lead_parts [53, 53] entry.symbol _ NoRelatedSymNews.tags.tail rfl (by decide +kernel)

structure NoLinesOfText where
  text : Terminated 1  -- tag 58

def NoLinesOfText.parts (record : NoLinesOfText) : List Part :=
  [Part.required [53, 56] record.text]

def NoLinesOfText.tags : List (List (List UInt8)) :=
  [[[53, 56]]]

theorem NoLinesOfText.shape (record : NoLinesOfText) : record.parts.map Part.tags = NoLinesOfText.tags := rfl

def NoLinesOfText.decode (tokens : List Token) : Option NoLinesOfText := do
  let text ← readRequired [53, 56] tokens
  pure { text }

theorem NoLinesOfText.decode_agrees (record : NoLinesOfText) (tokens : List Token)
    (agrees : ∀ tags ∈ NoLinesOfText.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoLinesOfText.decode tokens = some record := by
  have distinct : NoLinesOfText.tags.flatten.Nodup := by decide +kernel
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoLinesOfText.decode, text, some_bind] <;> rfl

theorem NoLinesOfText.taken (record : NoLinesOfText) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
   (paired_none pairing)

def NoLinesOfText.members : List (List UInt8) := NoLinesOfText.tags.flatten

def NoLinesOfText.encode (entry : NoLinesOfText) : List Token := encodeParts entry.parts

theorem NoLinesOfText.decode_encode (entry : NoLinesOfText) : NoLinesOfText.decode entry.encode = some entry :=
  NoLinesOfText.decode_agrees entry _ (fun _ _ => rfl)

theorem NoLinesOfText.within (entry : NoLinesOfText) : ∀ token ∈ entry.encode, token.tag ∈ NoLinesOfText.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoLinesOfText.shape] at this

theorem NoLinesOfText.led (entry : NoLinesOfText) : Lead [53, 56] entry.encode :=
  lead_parts [53, 56] entry.text _ NoLinesOfText.tags.tail rfl (by decide +kernel)

structure News where
  origTime : Option (Terminated 1)  -- tag 42
  headline : Terminated 1  -- tag 148
  noRelatedSymNews : List NoRelatedSymNews  -- tag 146
  noLinesOfText : List NoLinesOfText  -- tag 33
  newsStatus : Option (Terminated 1)  -- tag 20311

def News.parts (record : News) : List Part :=
  [Part.optional [52, 50] record.origTime,
   Part.required [49, 52, 56] record.headline,
   Part.group [49, 52, 54] NoRelatedSymNews.members NoRelatedSymNews.encode NoRelatedSymNews.within record.noRelatedSymNews,
   Part.group [51, 51] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within record.noLinesOfText,
   Part.optional [50, 48, 51, 49, 49] record.newsStatus]

def News.tags : List (List (List UInt8)) :=
  [[[52, 50]], [[49, 52, 56]], [49, 52, 54] :: NoRelatedSymNews.members, [51, 51] :: NoLinesOfText.members, [[50, 48, 51, 49, 49]]]

theorem News.shape (record : News) : record.parts.map Part.tags = News.tags := rfl

def News.decode (tokens : List Token) : Option News := do
  let origTime ← readOptional [52, 50] tokens
  let headline ← readRequired [49, 52, 56] tokens
  let noRelatedSymNews ← readGroup [49, 52, 54] [53, 53] NoRelatedSymNews.members NoRelatedSymNews.decode tokens
  let noLinesOfText ← readGroup [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.decode tokens
  let newsStatus ← readOptional [50, 48, 51, 49, 49] tokens
  pure { origTime, headline, noRelatedSymNews, noLinesOfText, newsStatus }

theorem News.decode_agrees (record : News) (tokens : List Token)
    (agrees : ∀ tags ∈ News.tags, select tags tokens = select tags (encodeParts record.parts)) :
    News.decode tokens = some record := by
  have distinct : News.tags.flatten.Nodup := by decide +kernel
  have origTime := readOptional_part [52, 50] record.origTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have headline := readRequired_part [49, 52, 56] record.headline tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noRelatedSymNews := readGroup_part [49, 52, 54] [53, 53] NoRelatedSymNews.members NoRelatedSymNews.encode NoRelatedSymNews.within NoRelatedSymNews.decode NoRelatedSymNews.decode_encode NoRelatedSymNews.led record.noRelatedSymNews tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noLinesOfText := readGroup_part [51, 51] [53, 56] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within NoLinesOfText.decode NoLinesOfText.decode_encode NoLinesOfText.led record.noLinesOfText tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have newsStatus := readOptional_part [50, 48, 51, 49, 49] record.newsStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [News.decode, origTime, headline, noRelatedSymNews, noLinesOfText, newsStatus, some_bind] <;> rfl

theorem News.taken (record : News) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 50] record.origTime (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 52, 56] record.headline (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [49, 52, 54] NoRelatedSymNews.members NoRelatedSymNews.encode NoRelatedSymNews.within (by decide) (by decide) NoRelatedSymNews.taken record.noRelatedSymNews)
     (paired_cons pairing _ _ (paired_group pairing [51, 51] NoLinesOfText.members NoLinesOfText.encode NoLinesOfText.within (by decide) (by decide) NoLinesOfText.taken record.noLinesOfText)
      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 51, 49, 49] record.newsStatus (by decide) (by decide))
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

structure NoTradePriceConditions where
  tradePriceCondition : Terminated 1  -- tag 5998

def NoTradePriceConditions.parts (record : NoTradePriceConditions) : List Part :=
  [Part.required [53, 57, 57, 56] record.tradePriceCondition]

def NoTradePriceConditions.tags : List (List (List UInt8)) :=
  [[[53, 57, 57, 56]]]

theorem NoTradePriceConditions.shape (record : NoTradePriceConditions) : record.parts.map Part.tags = NoTradePriceConditions.tags := rfl

def NoTradePriceConditions.decode (tokens : List Token) : Option NoTradePriceConditions := do
  let tradePriceCondition ← readRequired [53, 57, 57, 56] tokens
  pure { tradePriceCondition }

theorem NoTradePriceConditions.decode_agrees (record : NoTradePriceConditions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoTradePriceConditions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoTradePriceConditions.decode tokens = some record := by
  have distinct : NoTradePriceConditions.tags.flatten.Nodup := by decide +kernel
  have tradePriceCondition := readRequired_part [53, 57, 57, 56] record.tradePriceCondition tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoTradePriceConditions.decode, tradePriceCondition, some_bind] <;> rfl

theorem NoTradePriceConditions.taken (record : NoTradePriceConditions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 57, 57, 56] record.tradePriceCondition (by decide) (by decide))
   (paired_none pairing)

def NoTradePriceConditions.members : List (List UInt8) := NoTradePriceConditions.tags.flatten

def NoTradePriceConditions.encode (entry : NoTradePriceConditions) : List Token := encodeParts entry.parts

theorem NoTradePriceConditions.decode_encode (entry : NoTradePriceConditions) : NoTradePriceConditions.decode entry.encode = some entry :=
  NoTradePriceConditions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoTradePriceConditions.within (entry : NoTradePriceConditions) : ∀ token ∈ entry.encode, token.tag ∈ NoTradePriceConditions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoTradePriceConditions.shape] at this

theorem NoTradePriceConditions.led (entry : NoTradePriceConditions) : Lead [53, 57, 57, 56] entry.encode :=
  lead_parts [53, 57, 57, 56] entry.tradePriceCondition _ NoTradePriceConditions.tags.tail rfl (by decide +kernel)

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  pure { partyID, partyIDSource, partyRole }

theorem NoPartyIDs.decode_agrees (record : NoPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyIDs.decode tokens = some record := by
  have distinct : NoPartyIDs.tags.flatten.Nodup := by decide +kernel
  have partyID := readRequired_part [52, 52, 56] record.partyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyIDSource := readRequired_part [52, 52, 55] record.partyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyRole := readRequired_part [52, 53, 50] record.partyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, some_bind] <;> rfl

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 53, 50] record.partyRole (by decide) (by decide))
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

structure NoSides where
  side : Terminated 1  -- tag 54
  orderID : Terminated 1  -- tag 37
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradingSessionID : Terminated 1  -- tag 336

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.required [51, 55] record.orderID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [51, 51, 54] record.tradingSessionID]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[51, 55]], [52, 53, 51] :: NoPartyIDs.members, [[51, 51, 54]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let orderID ← readRequired [51, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  pure { side, orderID, noPartyIDs, tradingSessionID }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoSides.decode, side, orderID, noPartyIDs, tradingSessionID, some_bind] <;> rfl

theorem NoSides.taken (record : NoSides) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
     (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
      (paired_none pairing))))

def NoSides.members : List (List UInt8) := NoSides.tags.flatten

def NoSides.encode (entry : NoSides) : List Token := encodeParts entry.parts

theorem NoSides.decode_encode (entry : NoSides) : NoSides.decode entry.encode = some entry :=
  NoSides.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSides.within (entry : NoSides) : ∀ token ∈ entry.encode, token.tag ∈ NoSides.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSides.shape] at this

theorem NoSides.led (entry : NoSides) : Lead [53, 52] entry.encode :=
  lead_parts [53, 52] entry.side _ NoSides.tags.tail rfl (by decide +kernel)

structure TradeCaptureReport where
  tradeReportID : Terminated 1  -- tag 571
  secondaryTradeReportID : Option (Terminated 1)  -- tag 818
  secondaryTradeReportRefID : Option (Terminated 1)  -- tag 881
  tradeReportTransType : Terminated 1  -- tag 487
  tradeRequestID : Option (Terminated 1)  -- tag 568
  trdType : Terminated 1  -- tag 828
  trdSubType : Terminated 1  -- tag 829
  trdTypeBenchRef : Option (Terminated 1)  -- tag 830
  noTradePriceConditions : List NoTradePriceConditions  -- tag 5997
  reportedPxDiff : Option (Terminated 1)  -- tag 1134
  symbol : Option (Terminated 1)  -- tag 55
  securityID : Terminated 1  -- tag 48
  securityIDSource : Terminated 1  -- tag 22
  lastQty : Terminated 1  -- tag 32
  lastPx : Terminated 1  -- tag 31
  tradeDate : Terminated 1  -- tag 75
  transactTime : Option (Terminated 1)  -- tag 60
  settlDate : Option (Terminated 1)  -- tag 64
  text : Terminated 1  -- tag 58
  noSides : List NoSides  -- tag 552
  mMTLevel1 : Option (Terminated 1)  -- tag 6001
  mMTLevel2 : Option (Terminated 1)  -- tag 6002
  mMTLevel31 : Option (Terminated 1)  -- tag 6003
  mMTLevel32 : Option (Terminated 1)  -- tag 6004
  mMTLevel33 : Option (Terminated 1)  -- tag 6005
  mMTLevel34 : Option (Terminated 1)  -- tag 6006
  mMTLevel35 : Option (Terminated 1)  -- tag 6007
  mMTLevel36 : Option (Terminated 1)  -- tag 6008
  mMTLevel37 : Option (Terminated 1)  -- tag 6009
  mMTLevel38 : Option (Terminated 1)  -- tag 6010
  mMTLevel39 : Option (Terminated 1)  -- tag 6011
  mMTLevel41 : Option (Terminated 1)  -- tag 6012
  mMTLevel42 : Option (Terminated 1)  -- tag 6013
  mMTLevel5 : Option (Terminated 1)  -- tag 6014
  mMTConcatenated14Flags : Option (Terminated 1)  -- tag 6020
  transactionMIC : Option (Terminated 1)  -- tag 6050

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [56, 49, 56] record.secondaryTradeReportID,
   Part.optional [56, 56, 49] record.secondaryTradeReportRefID,
   Part.required [52, 56, 55] record.tradeReportTransType,
   Part.optional [53, 54, 56] record.tradeRequestID,
   Part.required [56, 50, 56] record.trdType,
   Part.required [56, 50, 57] record.trdSubType,
   Part.optional [56, 51, 48] record.trdTypeBenchRef,
   Part.group [53, 57, 57, 55] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within record.noTradePriceConditions,
   Part.optional [49, 49, 51, 52] record.reportedPxDiff,
   Part.optional [53, 53] record.symbol,
   Part.required [52, 56] record.securityID,
   Part.required [50, 50] record.securityIDSource,
   Part.required [51, 50] record.lastQty,
   Part.required [51, 49] record.lastPx,
   Part.required [55, 53] record.tradeDate,
   Part.optional [54, 48] record.transactTime,
   Part.optional [54, 52] record.settlDate,
   Part.required [53, 56] record.text,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.optional [54, 48, 48, 49] record.mMTLevel1,
   Part.optional [54, 48, 48, 50] record.mMTLevel2,
   Part.optional [54, 48, 48, 51] record.mMTLevel31,
   Part.optional [54, 48, 48, 52] record.mMTLevel32,
   Part.optional [54, 48, 48, 53] record.mMTLevel33,
   Part.optional [54, 48, 48, 54] record.mMTLevel34,
   Part.optional [54, 48, 48, 55] record.mMTLevel35,
   Part.optional [54, 48, 48, 56] record.mMTLevel36,
   Part.optional [54, 48, 48, 57] record.mMTLevel37,
   Part.optional [54, 48, 49, 48] record.mMTLevel38,
   Part.optional [54, 48, 49, 49] record.mMTLevel39,
   Part.optional [54, 48, 49, 50] record.mMTLevel41,
   Part.optional [54, 48, 49, 51] record.mMTLevel42,
   Part.optional [54, 48, 49, 52] record.mMTLevel5,
   Part.optional [54, 48, 50, 48] record.mMTConcatenated14Flags,
   Part.optional [54, 48, 53, 48] record.transactionMIC]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 55, 49]], [[56, 49, 56]], [[56, 56, 49]], [[52, 56, 55]], [[53, 54, 56]], [[56, 50, 56]], [[56, 50, 57]], [[56, 51, 48]], [53, 57, 57, 55] :: NoTradePriceConditions.members, [[49, 49, 51, 52]], [[53, 53]], [[52, 56]], [[50, 50]], [[51, 50]], [[51, 49]], [[55, 53]], [[54, 48]], [[54, 52]], [[53, 56]], [53, 53, 50] :: NoSides.members, [[54, 48, 48, 49]], [[54, 48, 48, 50]], [[54, 48, 48, 51]], [[54, 48, 48, 52]], [[54, 48, 48, 53]], [[54, 48, 48, 54]], [[54, 48, 48, 55]], [[54, 48, 48, 56]], [[54, 48, 48, 57]], [[54, 48, 49, 48]], [[54, 48, 49, 49]], [[54, 48, 49, 50]], [[54, 48, 49, 51]], [[54, 48, 49, 52]], [[54, 48, 50, 48]], [[54, 48, 53, 48]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let secondaryTradeReportID ← readOptional [56, 49, 56] tokens
  let secondaryTradeReportRefID ← readOptional [56, 56, 49] tokens
  let tradeReportTransType ← readRequired [52, 56, 55] tokens
  let tradeRequestID ← readOptional [53, 54, 56] tokens
  let trdType ← readRequired [56, 50, 56] tokens
  let trdSubType ← readRequired [56, 50, 57] tokens
  let trdTypeBenchRef ← readOptional [56, 51, 48] tokens
  let noTradePriceConditions ← readGroup [53, 57, 57, 55] [53, 57, 57, 56] NoTradePriceConditions.members NoTradePriceConditions.decode tokens
  let reportedPxDiff ← readOptional [49, 49, 51, 52] tokens
  let symbol ← readOptional [53, 53] tokens
  let securityID ← readRequired [52, 56] tokens
  let securityIDSource ← readRequired [50, 50] tokens
  let lastQty ← readRequired [51, 50] tokens
  let lastPx ← readRequired [51, 49] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let transactTime ← readOptional [54, 48] tokens
  let settlDate ← readOptional [54, 52] tokens
  let text ← readRequired [53, 56] tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let mMTLevel1 ← readOptional [54, 48, 48, 49] tokens
  let mMTLevel2 ← readOptional [54, 48, 48, 50] tokens
  let mMTLevel31 ← readOptional [54, 48, 48, 51] tokens
  let mMTLevel32 ← readOptional [54, 48, 48, 52] tokens
  let mMTLevel33 ← readOptional [54, 48, 48, 53] tokens
  let mMTLevel34 ← readOptional [54, 48, 48, 54] tokens
  let mMTLevel35 ← readOptional [54, 48, 48, 55] tokens
  let mMTLevel36 ← readOptional [54, 48, 48, 56] tokens
  let mMTLevel37 ← readOptional [54, 48, 48, 57] tokens
  let mMTLevel38 ← readOptional [54, 48, 49, 48] tokens
  let mMTLevel39 ← readOptional [54, 48, 49, 49] tokens
  let mMTLevel41 ← readOptional [54, 48, 49, 50] tokens
  let mMTLevel42 ← readOptional [54, 48, 49, 51] tokens
  let mMTLevel5 ← readOptional [54, 48, 49, 52] tokens
  let mMTConcatenated14Flags ← readOptional [54, 48, 50, 48] tokens
  let transactionMIC ← readOptional [54, 48, 53, 48] tokens
  pure { tradeReportID, secondaryTradeReportID, secondaryTradeReportRefID, tradeReportTransType, tradeRequestID, trdType, trdSubType, trdTypeBenchRef, noTradePriceConditions, reportedPxDiff, symbol, securityID, securityIDSource, lastQty, lastPx, tradeDate, transactTime, settlDate, text, noSides, mMTLevel1, mMTLevel2, mMTLevel31, mMTLevel32, mMTLevel33, mMTLevel34, mMTLevel35, mMTLevel36, mMTLevel37, mMTLevel38, mMTLevel39, mMTLevel41, mMTLevel42, mMTLevel5, mMTConcatenated14Flags, transactionMIC }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have secondaryTradeReportID := readOptional_part [56, 49, 56] record.secondaryTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have secondaryTradeReportRefID := readOptional_part [56, 56, 49] record.secondaryTradeReportRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeReportTransType := readRequired_part [52, 56, 55] record.tradeReportTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeRequestID := readOptional_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have trdSubType := readRequired_part [56, 50, 57] record.trdSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have trdTypeBenchRef := readOptional_part [56, 51, 48] record.trdTypeBenchRef tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noTradePriceConditions := readGroup_part [53, 57, 57, 55] [53, 57, 57, 56] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within NoTradePriceConditions.decode NoTradePriceConditions.decode_encode NoTradePriceConditions.led record.noTradePriceConditions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have reportedPxDiff := readOptional_part [49, 49, 51, 52] record.reportedPxDiff tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have securityID := readRequired_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have securityIDSource := readRequired_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have mMTLevel1 := readOptional_part [54, 48, 48, 49] record.mMTLevel1 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have mMTLevel2 := readOptional_part [54, 48, 48, 50] record.mMTLevel2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have mMTLevel31 := readOptional_part [54, 48, 48, 51] record.mMTLevel31 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have mMTLevel32 := readOptional_part [54, 48, 48, 52] record.mMTLevel32 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have mMTLevel33 := readOptional_part [54, 48, 48, 53] record.mMTLevel33 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have mMTLevel34 := readOptional_part [54, 48, 48, 54] record.mMTLevel34 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have mMTLevel35 := readOptional_part [54, 48, 48, 55] record.mMTLevel35 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have mMTLevel36 := readOptional_part [54, 48, 48, 56] record.mMTLevel36 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have mMTLevel37 := readOptional_part [54, 48, 48, 57] record.mMTLevel37 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have mMTLevel38 := readOptional_part [54, 48, 49, 48] record.mMTLevel38 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have mMTLevel39 := readOptional_part [54, 48, 49, 49] record.mMTLevel39 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have mMTLevel41 := readOptional_part [54, 48, 49, 50] record.mMTLevel41 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have mMTLevel42 := readOptional_part [54, 48, 49, 51] record.mMTLevel42 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have mMTLevel5 := readOptional_part [54, 48, 49, 52] record.mMTLevel5 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have mMTConcatenated14Flags := readOptional_part [54, 48, 50, 48] record.mMTConcatenated14Flags tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have transactionMIC := readOptional_part [54, 48, 53, 48] record.transactionMIC tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, tradeReportID, secondaryTradeReportID, secondaryTradeReportRefID, tradeReportTransType, tradeRequestID, trdType, trdSubType, trdTypeBenchRef, noTradePriceConditions, reportedPxDiff, symbol, securityID, securityIDSource, lastQty, lastPx, tradeDate, transactTime, settlDate, text, noSides, mMTLevel1, mMTLevel2, mMTLevel31, mMTLevel32, mMTLevel33, mMTLevel34, mMTLevel35, mMTLevel36, mMTLevel37, mMTLevel38, mMTLevel39, mMTLevel41, mMTLevel42, mMTLevel5, mMTConcatenated14Flags, transactionMIC, some_bind] <;> rfl

theorem TradeCaptureReport.taken (record : TradeCaptureReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 55, 49] record.tradeReportID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [56, 49, 56] record.secondaryTradeReportID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [56, 56, 49] record.secondaryTradeReportRefID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [52, 56, 55] record.tradeReportTransType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [56, 50, 56] record.trdType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [56, 50, 57] record.trdSubType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [56, 51, 48] record.trdTypeBenchRef (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [53, 57, 57, 55] NoTradePriceConditions.members NoTradePriceConditions.encode NoTradePriceConditions.within (by decide) (by decide) NoTradePriceConditions.taken record.noTradePriceConditions)
           (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 52] record.reportedPxDiff (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [53, 53] record.symbol (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [52, 56] record.securityID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_required pairing [50, 50] record.securityIDSource (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastQty (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [54, 48] record.transactTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.settlDate (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [53, 56] record.text (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSides.members NoSides.encode NoSides.within (by decide) (by decide) NoSides.taken record.noSides)
                      (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 49] record.mMTLevel1 (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 50] record.mMTLevel2 (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 51] record.mMTLevel31 (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 52] record.mMTLevel32 (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 53] record.mMTLevel33 (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 54] record.mMTLevel34 (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 55] record.mMTLevel35 (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 56] record.mMTLevel36 (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [54, 48, 48, 57] record.mMTLevel37 (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [54, 48, 49, 48] record.mMTLevel38 (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [54, 48, 49, 49] record.mMTLevel39 (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [54, 48, 49, 50] record.mMTLevel41 (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [54, 48, 49, 51] record.mMTLevel42 (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [54, 48, 49, 52] record.mMTLevel5 (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [54, 48, 50, 48] record.mMTConcatenated14Flags (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [54, 48, 53, 48] record.transactionMIC (by decide) (by decide))
                                      (paired_none pairing))))))))))))))))))))))))))))))))))))

structure TradeCaptureReportRequestAck where
  tradeRequestID : Terminated 1  -- tag 568
  tradeRequestType : Terminated 1  -- tag 569
  subscriptionRequestType : Option (Terminated 1)  -- tag 263
  tradeRequestResult : Terminated 1  -- tag 749
  tradeRequestStatus : Terminated 1  -- tag 750
  text : Option (Terminated 1)  -- tag 58

def TradeCaptureReportRequestAck.parts (record : TradeCaptureReportRequestAck) : List Part :=
  [Part.required [53, 54, 56] record.tradeRequestID,
   Part.required [53, 54, 57] record.tradeRequestType,
   Part.optional [50, 54, 51] record.subscriptionRequestType,
   Part.required [55, 52, 57] record.tradeRequestResult,
   Part.required [55, 53, 48] record.tradeRequestStatus,
   Part.optional [53, 56] record.text]

def TradeCaptureReportRequestAck.tags : List (List (List UInt8)) :=
  [[[53, 54, 56]], [[53, 54, 57]], [[50, 54, 51]], [[55, 52, 57]], [[55, 53, 48]], [[53, 56]]]

theorem TradeCaptureReportRequestAck.shape (record : TradeCaptureReportRequestAck) : record.parts.map Part.tags = TradeCaptureReportRequestAck.tags := rfl

def TradeCaptureReportRequestAck.decode (tokens : List Token) : Option TradeCaptureReportRequestAck := do
  let tradeRequestID ← readRequired [53, 54, 56] tokens
  let tradeRequestType ← readRequired [53, 54, 57] tokens
  let subscriptionRequestType ← readOptional [50, 54, 51] tokens
  let tradeRequestResult ← readRequired [55, 52, 57] tokens
  let tradeRequestStatus ← readRequired [55, 53, 48] tokens
  let text ← readOptional [53, 56] tokens
  pure { tradeRequestID, tradeRequestType, subscriptionRequestType, tradeRequestResult, tradeRequestStatus, text }

theorem TradeCaptureReportRequestAck.decode_agrees (record : TradeCaptureReportRequestAck) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReportRequestAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReportRequestAck.decode tokens = some record := by
  have distinct : TradeCaptureReportRequestAck.tags.flatten.Nodup := by decide +kernel
  have tradeRequestID := readRequired_part [53, 54, 56] record.tradeRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeRequestType := readRequired_part [53, 54, 57] record.tradeRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have subscriptionRequestType := readOptional_part [50, 54, 51] record.subscriptionRequestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradeRequestResult := readRequired_part [55, 52, 57] record.tradeRequestResult tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeRequestStatus := readRequired_part [55, 53, 48] record.tradeRequestStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [TradeCaptureReportRequestAck.decode, tradeRequestID, tradeRequestType, subscriptionRequestType, tradeRequestResult, tradeRequestStatus, text, some_bind] <;> rfl

theorem TradeCaptureReportRequestAck.taken (record : TradeCaptureReportRequestAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 54, 56] record.tradeRequestID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54, 57] record.tradeRequestType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 54, 51] record.subscriptionRequestType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [55, 52, 57] record.tradeRequestResult (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [55, 53, 48] record.tradeRequestStatus (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
        (paired_none pairing))))))

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketDataIncrementalRefresh (header : Header) (r0 : MarketDataIncrementalRefresh)
  | marketDataRequestReject (header : Header) (r0 : MarketDataRequestReject)
  | marketDataSnapshotFullRefresh (header : Header) (r0 : MarketDataSnapshotFullRefresh)
  | news (header : Header) (r0 : News)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataIncrementalRefresh header r0 => ⟨[51, 53], [88]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataRequestReject header r0 => ⟨[51, 53], [89]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketDataSnapshotFullRefresh header r0 => ⟨[51, 53], [87]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .news header r0 => ⟨[51, 53], [66]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], [65, 69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReportRequestAck header r0 => ⟨[51, 53], [65, 81]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [66] then
        if known (Header.tags ++ News.tags) rest then do
          let header ← Header.decode rest
          let r0 ← News.decode rest
          pure (.news header r0)
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
      else if token.value = [65, 69] then
        if known (Header.tags ++ TradeCaptureReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReport.decode rest
          pure (.tradeCaptureReport header r0)
        else none
      else if token.value = [65, 81] then
        if known (Header.tags ++ TradeCaptureReportRequestAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradeCaptureReportRequestAck.decode rest
          pure (.tradeCaptureReportRequestAck header r0)
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

theorem Message.decode_news (header : Header) (r0 : News) :
    Message.decode (Message.tokens (.news header r0)) = some (.news header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) rfl rfl (by decide +kernel))
  have c1 := News.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (News.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ News.tags) rfl
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

theorem Message.decode_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decode (Message.tokens (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decode (Message.tokens (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) rfl rfl (by decide +kernel))
  have c1 := TradeCaptureReportRequestAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradeCaptureReportRequestAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradeCaptureReportRequestAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decode_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decode_marketDataRequestReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decode_marketDataSnapshotFullRefresh header r0
  | news header r0 => exact Message.decode_news header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decode_tradeCaptureReportRequestAck header r0

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

theorem Message.decodeBytes_news (header : Header) (r0 : News) :
    Message.decodeBytes (Message.encode (.news header r0)) = some (.news header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (News.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_news header r0

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

theorem Message.decodeBytes_tradeCaptureReport (header : Header) (r0 : TradeCaptureReport) :
    Message.decodeBytes (Message.encode (.tradeCaptureReport header r0)) = some (.tradeCaptureReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReport header r0

theorem Message.decodeBytes_tradeCaptureReportRequestAck (header : Header) (r0 : TradeCaptureReportRequestAck) :
    Message.decodeBytes (Message.encode (.tradeCaptureReportRequestAck header r0)) = some (.tradeCaptureReportRequestAck header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65, 81]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradeCaptureReportRequestAck.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradeCaptureReportRequestAck header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketDataIncrementalRefresh header r0 => exact Message.decodeBytes_marketDataIncrementalRefresh header r0
  | marketDataRequestReject header r0 => exact Message.decodeBytes_marketDataRequestReject header r0
  | marketDataSnapshotFullRefresh header r0 => exact Message.decodeBytes_marketDataSnapshotFullRefresh header r0
  | news header r0 => exact Message.decodeBytes_news header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | tradeCaptureReportRequestAck header r0 => exact Message.decodeBytes_tradeCaptureReportRequestAck header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.AquisAquisstockexchangeMarketdataFixV105Exchange
