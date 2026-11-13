import Wire

/-!
# Chicago Board Options Exchange Purge v2.8, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.CboeBzxoptionsPurgeFixV28Exchange

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

structure ExecutionReport where
  massCancelID : Option (Terminated 1)  -- tag 7695
  cancelledOrderCount : Option (Terminated 1)  -- tag 7696

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.optional [55, 54, 57, 53] record.massCancelID,
   Part.optional [55, 54, 57, 54] record.cancelledOrderCount]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[[55, 54, 57, 53]], [[55, 54, 57, 54]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let massCancelID ← readOptional [55, 54, 57, 53] tokens
  let cancelledOrderCount ← readOptional [55, 54, 57, 54] tokens
  pure { massCancelID, cancelledOrderCount }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have massCancelID := readOptional_part [55, 54, 57, 53] record.massCancelID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have cancelledOrderCount := readOptional_part [55, 54, 57, 54] record.cancelledOrderCount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [ExecutionReport.decode, massCancelID, cancelledOrderCount, some_bind] <;> rfl

structure ExecutionReportPurgeAcknowledgement where
  execTransType : Option (Terminated 1)  -- tag 20

def ExecutionReportPurgeAcknowledgement.parts (record : ExecutionReportPurgeAcknowledgement) : List Part :=
  [Part.optional [50, 48] record.execTransType]

def ExecutionReportPurgeAcknowledgement.tags : List (List (List UInt8)) :=
  [[[50, 48]]]

theorem ExecutionReportPurgeAcknowledgement.shape (record : ExecutionReportPurgeAcknowledgement) : record.parts.map Part.tags = ExecutionReportPurgeAcknowledgement.tags := rfl

def ExecutionReportPurgeAcknowledgement.decode (tokens : List Token) : Option ExecutionReportPurgeAcknowledgement := do
  let execTransType ← readOptional [50, 48] tokens
  pure { execTransType }

theorem ExecutionReportPurgeAcknowledgement.decode_agrees (record : ExecutionReportPurgeAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPurgeAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPurgeAcknowledgement.decode tokens = some record := by
  have distinct : ExecutionReportPurgeAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have execTransType := readOptional_part [50, 48] record.execTransType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [ExecutionReportPurgeAcknowledgement.decode, execTransType, some_bind] <;> rfl

structure ExecutionReportPurgeNotification where
  transactTime : Option (Terminated 1)  -- tag 60
  matchingUnit : Option (Terminated 1)  -- tag 25017
  symbol : Option (Terminated 1)  -- tag 55
  lockOut : Option (Terminated 1)  -- tag 7697

def ExecutionReportPurgeNotification.parts (record : ExecutionReportPurgeNotification) : List Part :=
  [Part.optional [54, 48] record.transactTime,
   Part.optional [50, 53, 48, 49, 55] record.matchingUnit,
   Part.optional [53, 53] record.symbol,
   Part.optional [55, 54, 57, 55] record.lockOut]

def ExecutionReportPurgeNotification.tags : List (List (List UInt8)) :=
  [[[54, 48]], [[50, 53, 48, 49, 55]], [[53, 53]], [[55, 54, 57, 55]]]

theorem ExecutionReportPurgeNotification.shape (record : ExecutionReportPurgeNotification) : record.parts.map Part.tags = ExecutionReportPurgeNotification.tags := rfl

def ExecutionReportPurgeNotification.decode (tokens : List Token) : Option ExecutionReportPurgeNotification := do
  let transactTime ← readOptional [54, 48] tokens
  let matchingUnit ← readOptional [50, 53, 48, 49, 55] tokens
  let symbol ← readOptional [53, 53] tokens
  let lockOut ← readOptional [55, 54, 57, 55] tokens
  pure { transactTime, matchingUnit, symbol, lockOut }

theorem ExecutionReportPurgeNotification.decode_agrees (record : ExecutionReportPurgeNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReportPurgeNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReportPurgeNotification.decode tokens = some record := by
  have distinct : ExecutionReportPurgeNotification.tags.flatten.Nodup := by decide +kernel
  have transactTime := readOptional_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchingUnit := readOptional_part [50, 53, 48, 49, 55] record.matchingUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have lockOut := readOptional_part [55, 54, 57, 55] record.lockOut tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [ExecutionReportPurgeNotification.decode, transactTime, matchingUnit, symbol, lockOut, some_bind] <;> rfl

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
  | executionReportPurgeAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeAcknowledgement)
  | executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification)
  | purgeReject (header : Header) (r0 : PurgeReject)

def Message.tokens : Message → List Token
  | .executionReportPurgeAcknowledgement header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts)
  | .executionReportPurgeNotification header r0 r1 => ⟨[51, 53], ⟨[56], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts)
  | .purgeReject header r0 => ⟨[51, 53], ⟨[57], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [56] then
        match readRequired [49, 53, 48] rest with
        | none => none
        | some key =>
          if key.val = [77] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeAcknowledgement.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPurgeAcknowledgement.decode rest
              pure (.executionReportPurgeAcknowledgement header r0 r1)
            else none
          else if key.val = [80] then
            if known (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rest then do
              let header ← Header.decode rest
              let r0 ← ExecutionReport.decode rest
              let r1 ← ExecutionReportPurgeNotification.decode rest
              pure (.executionReportPurgeNotification header r0 r1)
            else none
          else none
      else if token.value.val = [57] then
        if known (Header.tags ++ PurgeReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← PurgeReject.decode rest
          pure (.purgeReject header r0)
        else none
      else none
    else none

theorem Message.decode_executionReportPurgeAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeAcknowledgement) :
    Message.decode (Message.tokens (.executionReportPurgeAcknowledgement header r0 r1)) = some (.executionReportPurgeAcknowledgement header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPurgeAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[77], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[77], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPurgeAcknowledgement.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPurgeAcknowledgement.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPurgeAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, some_bind] <;> rfl

theorem Message.decode_executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification) :
    Message.decode (Message.tokens (.executionReportPurgeNotification header r0 r1)) = some (.executionReportPurgeNotification header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) ([]) (Header.tags) (ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags) (ExecutionReport.tags) ([[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [49, 53, 48] ⟨[80], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) (Header.tags ++ ExecutionReport.tags) ([[[49, 53, 48]]]) (ExecutionReportPurgeNotification.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := ExecutionReportPurgeNotification.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩]) (r1.parts) ([]) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]]) (ExecutionReportPurgeNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_purgeReject (header : Header) (r0 : PurgeReject) :
    Message.decode (Message.tokens (.purgeReject header r0)) = some (.purgeReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (PurgeReject.tags) rfl rfl (by decide +kernel))
  have c1 := PurgeReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (PurgeReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ PurgeReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | executionReportPurgeAcknowledgement header r0 r1 => exact Message.decode_executionReportPurgeAcknowledgement header r0 r1
  | executionReportPurgeNotification header r0 r1 => exact Message.decode_executionReportPurgeNotification header r0 r1
  | purgeReject header r0 => exact Message.decode_purgeReject header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_executionReportPurgeAcknowledgement (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeAcknowledgement) :
    Message.decodeBytes (Message.encode (.executionReportPurgeAcknowledgement header r0 r1)) = some (.executionReportPurgeAcknowledgement header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[77], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPurgeAcknowledgement header r0 r1

theorem Message.decodeBytes_executionReportPurgeNotification (header : Header) (r0 : ExecutionReport) (r1 : ExecutionReportPurgeNotification) :
    Message.decodeBytes (Message.encode (.executionReportPurgeNotification header r0 r1)) = some (.executionReportPurgeNotification header r0 r1) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[56], by decide⟩⟩ (header.parts ++ r0.parts ++ [Part.required [49, 53, 48] ⟨[80], by decide⟩] ++ r1.parts) (Header.tags ++ ExecutionReport.tags ++ [[[49, 53, 48]]] ++ ExecutionReportPurgeNotification.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReportPurgeNotification header r0 r1

theorem Message.decodeBytes_purgeReject (header : Header) (r0 : PurgeReject) :
    Message.decodeBytes (Message.encode (.purgeReject header r0)) = some (.purgeReject header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[57], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ PurgeReject.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_purgeReject header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | executionReportPurgeAcknowledgement header r0 r1 => exact Message.decodeBytes_executionReportPurgeAcknowledgement header r0 r1
  | executionReportPurgeNotification header r0 r1 => exact Message.decodeBytes_executionReportPurgeNotification header r0 r1
  | purgeReject header r0 => exact Message.decodeBytes_purgeReject header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.CboeBzxoptionsPurgeFixV28Exchange
