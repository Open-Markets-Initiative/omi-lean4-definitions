import Wire

/-!
# Chicago Board Options Exchange Purge v1.3, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeCfefuturesPurgeFixV13Exchange

structure Header where
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Terminated 1  -- tag 50
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Terminated 1  -- tag 57
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
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
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
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
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompId ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompID, onBehalfOfSubID, deliverToCompId, deliverToSubID }

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
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have deliverToCompId := readOptional_part [49, 50, 56] record.deliverToCompId tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [Header.decode, senderCompID, senderSubID, targetCompID, targetSubID, msgSeqNum, possDupFlag, sendingTime, origSendingTime, onBehalfOfCompID, onBehalfOfSubID, deliverToCompId, deliverToSubID, some_bind] <;> rfl

structure PurgeAcknowledgement where
  execTransType : Option (Terminated 1)  -- tag 20
  execType : Option (Terminated 1)  -- tag 150
  massCancelID : Option (Terminated 1)  -- tag 7695

def PurgeAcknowledgement.parts (record : PurgeAcknowledgement) : List Part :=
  [Part.optional [50, 48] record.execTransType,
   Part.optional [49, 53, 48] record.execType,
   Part.optional [55, 54, 57, 53] record.massCancelID]

def PurgeAcknowledgement.tags : List (List (List UInt8)) :=
  [[[50, 48]], [[49, 53, 48]], [[55, 54, 57, 53]]]

theorem PurgeAcknowledgement.shape (record : PurgeAcknowledgement) : record.parts.map Part.tags = PurgeAcknowledgement.tags := rfl

def PurgeAcknowledgement.decode (tokens : List Token) : Option PurgeAcknowledgement := do
  let execTransType ← readOptional [50, 48] tokens
  let execType ← readOptional [49, 53, 48] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  pure { execTransType, execType, massCancelID }

theorem PurgeAcknowledgement.decode_agrees (record : PurgeAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ PurgeAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PurgeAcknowledgement.decode tokens = some record := by
  have distinct : PurgeAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execType := readOptional_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [PurgeAcknowledgement.decode, execTransType, execType, massCancelID, some_bind] <;> rfl

structure PurgeReject where
  ordStatus : Option (Terminated 1)  -- tag 39
  cxlRejResponseTo : Option (Terminated 1)  -- tag 434
  cxlRejReason : Option (Terminated 1)  -- tag 102
  text : Option (Terminated 1)  -- tag 58
  massCancelID : Option (Terminated 1)  -- tag 7695

def PurgeReject.parts (record : PurgeReject) : List Part :=
  [Part.optional [51, 57] record.ordStatus,
   Part.optional [52, 51, 52] record.cxlRejResponseTo,
   Part.optional [49, 48, 50] record.cxlRejReason,
   Part.optional [53, 56] record.text,
   Part.optional [55, 54, 57, 53] record.massCancelID]

def PurgeReject.tags : List (List (List UInt8)) :=
  [[[51, 57]], [[52, 51, 52]], [[49, 48, 50]], [[53, 56]], [[55, 54, 57, 53]]]

theorem PurgeReject.shape (record : PurgeReject) : record.parts.map Part.tags = PurgeReject.tags := rfl

def PurgeReject.decode (tokens : List Token) : Option PurgeReject := do
  let ordStatus ← readOptional [51, 57] tokens
  let cxlRejResponseTo ← readOptional [52, 51, 52] tokens
  let cxlRejReason ← readOptional [49, 48, 50] tokens
  let text ← readOptional [53, 56] tokens
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  pure { ordStatus, cxlRejResponseTo, cxlRejReason, text, massCancelID }

theorem PurgeReject.decode_agrees (record : PurgeReject) (tokens : List Token)
    (agrees : ∀ tags ∈ PurgeReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    PurgeReject.decode tokens = some record := by
  have distinct : PurgeReject.tags.flatten.Nodup := by decide +kernel
  have ordStatus := readOptional_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have cxlRejResponseTo := readOptional_part [52, 51, 52] record.cxlRejResponseTo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cxlRejReason := readOptional_part [49, 48, 50] record.cxlRejReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [PurgeReject.decode, ordStatus, cxlRejResponseTo, cxlRejReason, text, massCancelID, some_bind] <;> rfl

inductive Message where
  | purgeAcknowledgement (header : Header) (r0 : PurgeAcknowledgement)
  | purgeReject (header : Header) (r0 : PurgeReject)

def Message.tokens : Message → List Token
  | .purgeAcknowledgement header r0 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .purgeReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        if known (Header.tags ++ PurgeAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PurgeAcknowledgement.decode rest
          pure (.purgeAcknowledgement header r0)
        else none
      else if token.value.val = [57] then
        if known (Header.tags ++ PurgeReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PurgeReject.decode rest
          pure (.purgeReject header r0)
        else none
      else none
    else none

theorem Message.decode_purgeAcknowledgement (header : Header) (r0 : PurgeAcknowledgement) :
    Message.decode (Message.tokens (.purgeAcknowledgement header r0)) = some (.purgeAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PurgeAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := PurgeAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PurgeAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PurgeAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_purgeReject (header : Header) (r0 : PurgeReject) :
    Message.decode (Message.tokens (.purgeReject header r0)) = some (.purgeReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PurgeReject.tags) rfl rfl (by decide +kernel))
  have c1 := PurgeReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PurgeReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PurgeReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | purgeAcknowledgement header r0 => exact Message.decode_purgeAcknowledgement header r0
  | purgeReject header r0 => exact Message.decode_purgeReject header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_purgeAcknowledgement (header : Header) (r0 : PurgeAcknowledgement) :
    Message.decodeBytes (Message.encode (.purgeAcknowledgement header r0)) = some (.purgeAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PurgeAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_purgeAcknowledgement header r0

theorem Message.decodeBytes_purgeReject (header : Header) (r0 : PurgeReject) :
    Message.decodeBytes (Message.encode (.purgeReject header r0)) = some (.purgeReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PurgeReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_purgeReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | purgeAcknowledgement header r0 => exact Message.decodeBytes_purgeAcknowledgement header r0
  | purgeReject header r0 => exact Message.decodeBytes_purgeReject header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeCfefuturesPurgeFixV13Exchange
