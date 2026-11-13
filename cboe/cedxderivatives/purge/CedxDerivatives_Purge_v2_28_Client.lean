import Wire

/-!
# Chicago Board Options Exchange Purge v2.28, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCedxderivativesPurgeFixV228Client

structure Header where
  msgSeqNum : Option (Terminated 1)  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Option (Terminated 1)  -- tag 49
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  origSendingTime : Option (Terminated 1)  -- tag 122
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.optional [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 50] record.origSendingTime,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 50]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readOptional [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readOptional_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderCompID := readOptional_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, targetSubID, possResend, onBehalfOfCompID, onBehalfOfSubID, origSendingTime, deliverToCompID, deliverToSubID, some_bind] <;> rfl

structure CustomGroupIDCnt where
  customGroupID : Terminated 1  -- tag 7699

def CustomGroupIDCnt.parts (record : CustomGroupIDCnt) : List Part :=
  [Part.required [55, 54, 57, 57] record.customGroupID]

def CustomGroupIDCnt.tags : List (List (List UInt8)) :=
  [[[55, 54, 57, 57]]]

theorem CustomGroupIDCnt.shape (record : CustomGroupIDCnt) : record.parts.map Part.tags = CustomGroupIDCnt.tags := rfl

def CustomGroupIDCnt.decode (tokens : List Token) : Option CustomGroupIDCnt := do
  let customGroupID ← readRequired [55, 54, 57, 57] tokens
  pure { customGroupID }

theorem CustomGroupIDCnt.decode_agrees (record : CustomGroupIDCnt) (tokens : List Token)
    (agrees : ∀ tags ∈ CustomGroupIDCnt.tags, select tags tokens = select tags (encodeParts record.parts)) :
    CustomGroupIDCnt.decode tokens = some record := by
  have distinct : CustomGroupIDCnt.tags.flatten.Nodup := by decide +kernel
  have customGroupID := readRequired_part [55, 54, 57, 57] record.customGroupID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [CustomGroupIDCnt.decode, customGroupID, some_bind] <;> rfl

def CustomGroupIDCnt.members : List (List UInt8) := CustomGroupIDCnt.tags.flatten

def CustomGroupIDCnt.encode (entry : CustomGroupIDCnt) : List Token := encodeParts entry.parts

theorem CustomGroupIDCnt.decode_encode (entry : CustomGroupIDCnt) : CustomGroupIDCnt.decode entry.encode = some entry :=
  CustomGroupIDCnt.decode_agrees entry _ (fun _ _ => rfl)

theorem CustomGroupIDCnt.within (entry : CustomGroupIDCnt) : ∀ token ∈ entry.encode, token.tag ∈ CustomGroupIDCnt.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [CustomGroupIDCnt.shape] at this

theorem CustomGroupIDCnt.led (entry : CustomGroupIDCnt) : Lead [55, 54, 57, 57] entry.encode :=
  lead_parts [55, 54, 57, 57] entry.customGroupID _ CustomGroupIDCnt.tags.tail rfl (by decide +kernel)

structure PurgeRequest where
  transactTime : Option (Terminated 1)  -- tag 60
  symbol : Option (Terminated 1)  -- tag 55
  massCancelInst : Option (Terminated 1)  -- tag 7700
  massCancelID : Option (Terminated 1)  -- tag 7695
  customGroupIDCnt : List CustomGroupIDCnt  -- tag 7698

def PurgeRequest.parts (record : PurgeRequest) : List Part :=
  [Part.optional [54, 48] record.transactTime,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 55, 48, 48] record.massCancelInst,
   Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.group [55, 54, 57, 56] CustomGroupIDCnt.members CustomGroupIDCnt.encode CustomGroupIDCnt.within record.customGroupIDCnt]

def PurgeRequest.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[53, 53]], [[55, 55, 48, 48]], [[55, 54, 57, 53]], [55, 54, 57, 56] :: CustomGroupIDCnt.members]

theorem PurgeRequest.shape (record : PurgeRequest) : record.parts.map Part.tags = PurgeRequest.tags := rfl

def PurgeRequest.decode (tokens : List Token) : Option PurgeRequest := do
  let transactTime ← readOptional [54, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let massCancelInst ← readOptional [55, 55, 48, 48] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let customGroupIDCnt ← readGroup [55, 54, 57, 56] [55, 54, 57, 57] CustomGroupIDCnt.members CustomGroupIDCnt.decode tokens
  pure { transactTime, symbol, massCancelInst, massCancelID, customGroupIDCnt }

theorem PurgeRequest.decode_agrees (record : PurgeRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ PurgeRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PurgeRequest.decode tokens = some record := by
  have distinct : PurgeRequest.tags.flatten.Nodup := by decide +kernel
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelInst := readOptional_part [55, 55, 48, 48] record.massCancelInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have customGroupIDCnt := readGroup_part [55, 54, 57, 56] [55, 54, 57, 57] CustomGroupIDCnt.members CustomGroupIDCnt.encode CustomGroupIDCnt.within CustomGroupIDCnt.decode CustomGroupIDCnt.decode_encode CustomGroupIDCnt.led record.customGroupIDCnt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [PurgeRequest.decode, transactTime, symbol, massCancelInst, massCancelID, customGroupIDCnt, some_bind] <;> rfl

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

end Omi.CboeCedxderivativesPurgeFixV228Client
