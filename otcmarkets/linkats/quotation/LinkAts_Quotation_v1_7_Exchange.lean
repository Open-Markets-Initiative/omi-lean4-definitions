import Wire

/-!
# OTC Markets Group Quotation v1.7, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.OtcmarketsLinkatsQuotationFixV17Exchange

structure Header where
  msgSeqNum : Option (Terminated 1)  -- tag 34
  senderCompID : Option (Terminated 1)  -- tag 49
  sendingTime : Option (Terminated 1)  -- tag 52
  targetCompID : Option (Terminated 1)  -- tag 56
  onBehalfOfCompID : Option (Terminated 1)  -- tag 115
  onBehalfOfSubID : Option (Terminated 1)  -- tag 116
  deliverToCompID : Option (Terminated 1)  -- tag 128
  deliverToSubID : Option (Terminated 1)  -- tag 129

def Header.parts (record : Header) : List Part :=
  [Part.optional [51, 52] record.msgSeqNum,
   Part.optional [52, 57] record.senderCompID,
   Part.optional [53, 50] record.sendingTime,
   Part.optional [53, 54] record.targetCompID,
   Part.optional [49, 49, 53] record.onBehalfOfCompID,
   Part.optional [49, 49, 54] record.onBehalfOfSubID,
   Part.optional [49, 50, 56] record.deliverToCompID,
   Part.optional [49, 50, 57] record.deliverToSubID]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 57]], [[53, 50]], [[53, 54]], [[49, 49, 53]], [[49, 49, 54]], [[49, 50, 56]], [[49, 50, 57]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readOptional [51, 52] tokens
  let senderCompID ← readOptional [52, 57] tokens
  let sendingTime ← readOptional [53, 50] tokens
  let targetCompID ← readOptional [53, 54] tokens
  let onBehalfOfCompID ← readOptional [49, 49, 53] tokens
  let onBehalfOfSubID ← readOptional [49, 49, 54] tokens
  let deliverToCompID ← readOptional [49, 50, 56] tokens
  let deliverToSubID ← readOptional [49, 50, 57] tokens
  pure { msgSeqNum, senderCompID, sendingTime, targetCompID, onBehalfOfCompID, onBehalfOfSubID, deliverToCompID, deliverToSubID }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readOptional_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderCompID := readOptional_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sendingTime := readOptional_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have targetCompID := readOptional_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have onBehalfOfCompID := readOptional_part [49, 49, 53] record.onBehalfOfCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have onBehalfOfSubID := readOptional_part [49, 49, 54] record.onBehalfOfSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliverToCompID := readOptional_part [49, 50, 56] record.deliverToCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have deliverToSubID := readOptional_part [49, 50, 57] record.deliverToSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, senderCompID, sendingTime, targetCompID, onBehalfOfCompID, onBehalfOfSubID, deliverToCompID, deliverToSubID, some_bind] <;> rfl

structure QuoteAcknowledgement where
  msgRefID : Terminated 1  -- tag 9670
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  resultCode : Terminated 1  -- tag 9548
  text : Terminated 1  -- tag 58
  quoteID : Terminated 1  -- tag 9690
  cATroutedQuoteID : Option (Terminated 1)  -- tag 9695

def QuoteAcknowledgement.parts (record : QuoteAcknowledgement) : List Part :=
  [Part.required [57, 54, 55, 48] record.msgRefID,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.required [57, 53, 52, 56] record.resultCode,
   Part.required [53, 56] record.text,
   Part.required [57, 54, 57, 48] record.quoteID,
   Part.optional [57, 54, 57, 53] record.cATroutedQuoteID]

def QuoteAcknowledgement.tags : List (List (List UInt8)) :=
  [[[57, 54, 55, 48]], [[53, 53]], [[54, 53]], [[57, 53, 52, 56]], [[53, 56]], [[57, 54, 57, 48]], [[57, 54, 57, 53]]]

theorem QuoteAcknowledgement.shape (record : QuoteAcknowledgement) : record.parts.map Part.tags = QuoteAcknowledgement.tags := rfl

def QuoteAcknowledgement.decode (tokens : List Token) : Option QuoteAcknowledgement := do
  let msgRefID ← readRequired [57, 54, 55, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let resultCode ← readRequired [57, 53, 52, 56] tokens
  let text ← readRequired [53, 56] tokens
  let quoteID ← readRequired [57, 54, 57, 48] tokens
  let cATroutedQuoteID ← readOptional [57, 54, 57, 53] tokens
  pure { msgRefID, symbol, symbolSfx, resultCode, text, quoteID, cATroutedQuoteID }

theorem QuoteAcknowledgement.decode_agrees (record : QuoteAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteAcknowledgement.decode tokens = some record := by
  have distinct : QuoteAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have msgRefID := readRequired_part [57, 54, 55, 48] record.msgRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have resultCode := readRequired_part [57, 53, 52, 56] record.resultCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have quoteID := readRequired_part [57, 54, 57, 48] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cATroutedQuoteID := readOptional_part [57, 54, 57, 53] record.cATroutedQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [QuoteAcknowledgement.decode, msgRefID, symbol, symbolSfx, resultCode, text, quoteID, cATroutedQuoteID, some_bind] <;> rfl

structure TraderStateAcknowledgement where
  msgRefID : Terminated 1  -- tag 9670
  resultCode : Terminated 1  -- tag 9548
  text : Terminated 1  -- tag 58

def TraderStateAcknowledgement.parts (record : TraderStateAcknowledgement) : List Part :=
  [Part.required [57, 54, 55, 48] record.msgRefID,
   Part.required [57, 53, 52, 56] record.resultCode,
   Part.required [53, 56] record.text]

def TraderStateAcknowledgement.tags : List (List (List UInt8)) :=
  [[[57, 54, 55, 48]], [[57, 53, 52, 56]], [[53, 56]]]

theorem TraderStateAcknowledgement.shape (record : TraderStateAcknowledgement) : record.parts.map Part.tags = TraderStateAcknowledgement.tags := rfl

def TraderStateAcknowledgement.decode (tokens : List Token) : Option TraderStateAcknowledgement := do
  let msgRefID ← readRequired [57, 54, 55, 48] tokens
  let resultCode ← readRequired [57, 53, 52, 56] tokens
  let text ← readRequired [53, 56] tokens
  pure { msgRefID, resultCode, text }

theorem TraderStateAcknowledgement.decode_agrees (record : TraderStateAcknowledgement) (tokens : List Token)
    (agrees : ∀ tags ∈ TraderStateAcknowledgement.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TraderStateAcknowledgement.decode tokens = some record := by
  have distinct : TraderStateAcknowledgement.tags.flatten.Nodup := by decide +kernel
  have msgRefID := readRequired_part [57, 54, 55, 48] record.msgRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have resultCode := readRequired_part [57, 53, 52, 56] record.resultCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have text := readRequired_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [TraderStateAcknowledgement.decode, msgRefID, resultCode, text, some_bind] <;> rfl

inductive Message where
  | quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement)
  | traderStateAcknowledgement (header : Header) (r0 : TraderStateAcknowledgement)

def Message.tokens : Message → List Token
  | .quoteAcknowledgement header r0 => ⟨[51, 53], ⟨[98], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .traderStateAcknowledgement header r0 => ⟨[51, 53], ⟨[79, 84, 65], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [98] then
        if known (Header.tags ++ QuoteAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteAcknowledgement.decode rest
          pure (.quoteAcknowledgement header r0)
        else none
      else if token.value.val = [79, 84, 65] then
        if known (Header.tags ++ TraderStateAcknowledgement.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TraderStateAcknowledgement.decode rest
          pure (.traderStateAcknowledgement header r0)
        else none
      else none
    else none

theorem Message.decode_quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement) :
    Message.decode (Message.tokens (.quoteAcknowledgement header r0)) = some (.quoteAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_traderStateAcknowledgement (header : Header) (r0 : TraderStateAcknowledgement) :
    Message.decode (Message.tokens (.traderStateAcknowledgement header r0)) = some (.traderStateAcknowledgement header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TraderStateAcknowledgement.tags) rfl rfl (by decide +kernel))
  have c1 := TraderStateAcknowledgement.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TraderStateAcknowledgement.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TraderStateAcknowledgement.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | quoteAcknowledgement header r0 => exact Message.decode_quoteAcknowledgement header r0
  | traderStateAcknowledgement header r0 => exact Message.decode_traderStateAcknowledgement header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_quoteAcknowledgement (header : Header) (r0 : QuoteAcknowledgement) :
    Message.decodeBytes (Message.encode (.quoteAcknowledgement header r0)) = some (.quoteAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[98], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteAcknowledgement header r0

theorem Message.decodeBytes_traderStateAcknowledgement (header : Header) (r0 : TraderStateAcknowledgement) :
    Message.decodeBytes (Message.encode (.traderStateAcknowledgement header r0)) = some (.traderStateAcknowledgement header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[79, 84, 65], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TraderStateAcknowledgement.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_traderStateAcknowledgement header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | quoteAcknowledgement header r0 => exact Message.decodeBytes_quoteAcknowledgement header r0
  | traderStateAcknowledgement header r0 => exact Message.decodeBytes_traderStateAcknowledgement header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.OtcmarketsLinkatsQuotationFixV17Exchange
