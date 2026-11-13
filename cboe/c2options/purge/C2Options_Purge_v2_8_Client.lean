import Wire

/-!
# Chicago Board Options Exchange Purge v2.8, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeC2optionsPurgeFixV28Client

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompId : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  deliverToCompId : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 48] record.senderSubID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 55] record.targetSubID,
   Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 49, 53] record.onBehalfOfCompId,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 56] record.deliverToCompId,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 48]], [[53, 54]], [[53, 55]], [[51, 52]], [[52, 51]], [[53, 50]], [[49, 50, 50]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readRequired [53, 48] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readRequired [53, 55] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let onBehalfOfCompId ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompId ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderSubID := readRequired_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetSubID := readRequired_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfCompId := readOptional_part [49, 49, 53] record.onBehalfOfCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompId := readOptional_part [49, 50, 56] record.deliverToCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompId, onBehalfOfSubID, deliverToCompId, deliverToSubID, some_bind] <;> rfl

structure PurgeRequest where
  possResend : Option (Terminated 1)  -- tag 97
  routingFirmID : Option (Terminated 1)  -- tag 7933
  transactTime : Terminated 1  -- tag 60
  massCancelInst : Terminated 1  -- tag 7700
  massCancelID : Option (Terminated 1)  -- tag 7695
  symbol : Option (Terminated 1)  -- tag 55
  customGroupIDCnt : Option (Terminated 1)  -- tag 7698
  customGroupID : Option (Terminated 1)  -- tag 7699
  matchingUnit : Option (Terminated 1)  -- tag 25017

def PurgeRequest.parts (record : PurgeRequest) : List Part :=
  [Part.optional [57, 55] record.possResend,
   Part.optional [55, 57, 51, 51] record.routingFirmID,
   Part.required [54, 48] record.transactTime,
   Part.required [55, 55, 48, 48] record.massCancelInst,
   Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 54, 57, 56] record.customGroupIDCnt,
   Part.optional [55, 54, 57, 57] record.customGroupID,
   Part.optional [50, 53, 48, 49, 55] record.matchingUnit]

def PurgeRequest.tags : List (List (List UInt8)) :=
  [[[57, 55]], [[55, 57, 51, 51]], [[54, 48]], [[55, 55, 48, 48]], [[55, 54, 57, 53]], [[53, 53]], [[55, 54, 57, 56]], [[55, 54, 57, 57]], [[50, 53, 48, 49, 55]]]

theorem PurgeRequest.shape (record : PurgeRequest) : record.parts.map Part.tags = PurgeRequest.tags := rfl

def PurgeRequest.decode (tokens : List Token) : Option PurgeRequest := do
  let possResend ← readOptional [57, 55] tokens
  let routingFirmID ← readOptional [55, 57, 51, 51] tokens
  let transactTime ← readRequired [54, 48] tokens
  let massCancelInst ← readRequired [55, 55, 48, 48] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let symbol ← readOptional [53, 53] tokens
  let customGroupIDCnt ← readOptional [55, 54, 57, 56] tokens
  let customGroupID ← readOptional [55, 54, 57, 57] tokens
  let matchingUnit ← readOptional [50, 53, 48, 49, 55] tokens
  pure { possResend, routingFirmID, transactTime, massCancelInst, massCancelID, symbol, customGroupIDCnt, customGroupID, matchingUnit }

theorem PurgeRequest.decode_agrees (record : PurgeRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ PurgeRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PurgeRequest.decode tokens = some record := by
  have distinct : PurgeRequest.tags.flatten.Nodup := by decide +kernel
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have routingFirmID := readOptional_part [55, 57, 51, 51] record.routingFirmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have massCancelInst := readRequired_part [55, 55, 48, 48] record.massCancelInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have customGroupIDCnt := readOptional_part [55, 54, 57, 56] record.customGroupIDCnt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have customGroupID := readOptional_part [55, 54, 57, 57] record.customGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have matchingUnit := readOptional_part [50, 53, 48, 49, 55] record.matchingUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [PurgeRequest.decode, possResend, routingFirmID, transactTime, massCancelInst, massCancelID, symbol, customGroupIDCnt, customGroupID, matchingUnit, some_bind] <;> rfl

inductive Message where
  | purgeRequest (header : Header) (r0 : PurgeRequest)

def Message.tokens : Message → List Token
  | .purgeRequest header r0 => ⟨[51, 53], ⟨[70], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [70] then
        if known (Header.tags ++ PurgeRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PurgeRequest.decode rest
          pure (.purgeRequest header r0)
        else none
      else none
    else none

theorem Message.decode_purgeRequest (header : Header) (r0 : PurgeRequest) :
    Message.decode (Message.tokens (.purgeRequest header r0)) = some (.purgeRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PurgeRequest.tags) rfl rfl (by decide +kernel))
  have c1 := PurgeRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PurgeRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PurgeRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | purgeRequest header r0 => exact Message.decode_purgeRequest header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_purgeRequest (header : Header) (r0 : PurgeRequest) :
    Message.decodeBytes (Message.encode (.purgeRequest header r0)) = some (.purgeRequest header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[70], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PurgeRequest.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_purgeRequest header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | purgeRequest header r0 => exact Message.decodeBytes_purgeRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeC2optionsPurgeFixV28Client
