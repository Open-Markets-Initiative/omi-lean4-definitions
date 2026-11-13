import Wire

/-!
# OTC Markets Group Quotation v1.7, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.OtcmarketsLinkatsQuotationFixV17Client

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

structure Quote where
  msgRefID : Option (Terminated 1)  -- tag 9670
  updateType : Terminated 1  -- tag 9540
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22
  aTSOnly : Terminated 1  -- tag 9595
  cATroutedQuoteID : Option (Terminated 1)  -- tag 9695
  bidPriceType : Option (Terminated 1)  -- tag 9501
  bidPx : Option (Terminated 1)  -- tag 132
  bidSize : Option (Terminated 1)  -- tag 134
  bidQAPRate : Option (Terminated 1)  -- tag 9662
  bidAutoEx : Option (Terminated 1)  -- tag 9680
  offerPriceType : Option (Terminated 1)  -- tag 9502
  offerPx : Option (Terminated 1)  -- tag 133
  offerSize : Option (Terminated 1)  -- tag 135
  offerQAPRate : Option (Terminated 1)  -- tag 9663
  offerAutoEx : Option (Terminated 1)  -- tag 9681
  lockCrossFlag : Option (Terminated 1)  -- tag 9506
  unsolicited : Option (Terminated 1)  -- tag 9534
  nonAffiliate : Option (Terminated 1)  -- tag 9535
  cancelTime : Option (Terminated 1)  -- tag 9596
  autoCancelEOD : Option (Terminated 1)  -- tag 9597

def Quote.parts (record : Quote) : List Part :=
  [Part.optional [57, 54, 55, 48] record.msgRefID,
   Part.required [57, 53, 52, 48] record.updateType,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource,
   Part.required [57, 53, 57, 53] record.aTSOnly,
   Part.optional [57, 54, 57, 53] record.cATroutedQuoteID,
   Part.optional [57, 53, 48, 49] record.bidPriceType,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [57, 54, 54, 50] record.bidQAPRate,
   Part.optional [57, 54, 56, 48] record.bidAutoEx,
   Part.optional [57, 53, 48, 50] record.offerPriceType,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 53] record.offerSize,
   Part.optional [57, 54, 54, 51] record.offerQAPRate,
   Part.optional [57, 54, 56, 49] record.offerAutoEx,
   Part.optional [57, 53, 48, 54] record.lockCrossFlag,
   Part.optional [57, 53, 51, 52] record.unsolicited,
   Part.optional [57, 53, 51, 53] record.nonAffiliate,
   Part.optional [57, 53, 57, 54] record.cancelTime,
   Part.optional [57, 53, 57, 55] record.autoCancelEOD]

def Quote.tags : List (List (List UInt8)) :=
  [[[57, 54, 55, 48]], [[57, 53, 52, 48]], [[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]], [[57, 53, 57, 53]], [[57, 54, 57, 53]], [[57, 53, 48, 49]], [[49, 51, 50]], [[49, 51, 52]], [[57, 54, 54, 50]], [[57, 54, 56, 48]], [[57, 53, 48, 50]], [[49, 51, 51]], [[49, 51, 53]], [[57, 54, 54, 51]], [[57, 54, 56, 49]], [[57, 53, 48, 54]], [[57, 53, 51, 52]], [[57, 53, 51, 53]], [[57, 53, 57, 54]], [[57, 53, 57, 55]]]

theorem Quote.shape (record : Quote) : record.parts.map Part.tags = Quote.tags := rfl

def Quote.decode (tokens : List Token) : Option Quote := do
  let msgRefID ← readOptional [57, 54, 55, 48] tokens
  let updateType ← readRequired [57, 53, 52, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  let aTSOnly ← readRequired [57, 53, 57, 53] tokens
  let cATroutedQuoteID ← readOptional [57, 54, 57, 53] tokens
  let bidPriceType ← readOptional [57, 53, 48, 49] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let bidQAPRate ← readOptional [57, 54, 54, 50] tokens
  let bidAutoEx ← readOptional [57, 54, 56, 48] tokens
  let offerPriceType ← readOptional [57, 53, 48, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  let offerQAPRate ← readOptional [57, 54, 54, 51] tokens
  let offerAutoEx ← readOptional [57, 54, 56, 49] tokens
  let lockCrossFlag ← readOptional [57, 53, 48, 54] tokens
  let unsolicited ← readOptional [57, 53, 51, 52] tokens
  let nonAffiliate ← readOptional [57, 53, 51, 53] tokens
  let cancelTime ← readOptional [57, 53, 57, 54] tokens
  let autoCancelEOD ← readOptional [57, 53, 57, 55] tokens
  pure { msgRefID, updateType, symbol, symbolSfx, securityID, iDSource, aTSOnly, cATroutedQuoteID, bidPriceType, bidPx, bidSize, bidQAPRate, bidAutoEx, offerPriceType, offerPx, offerSize, offerQAPRate, offerAutoEx, lockCrossFlag, unsolicited, nonAffiliate, cancelTime, autoCancelEOD }

theorem Quote.decode_agrees (record : Quote) (tokens : List Token)
    (agrees : ∀ tags ∈ Quote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Quote.decode tokens = some record := by
  have distinct : Quote.tags.flatten.Nodup := by decide +kernel
  have msgRefID := readOptional_part [57, 54, 55, 48] record.msgRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have updateType := readRequired_part [57, 53, 52, 48] record.updateType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have aTSOnly := readRequired_part [57, 53, 57, 53] record.aTSOnly tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cATroutedQuoteID := readOptional_part [57, 54, 57, 53] record.cATroutedQuoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have bidPriceType := readOptional_part [57, 53, 48, 49] record.bidPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have bidQAPRate := readOptional_part [57, 54, 54, 50] record.bidQAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have bidAutoEx := readOptional_part [57, 54, 56, 48] record.bidAutoEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have offerPriceType := readOptional_part [57, 53, 48, 50] record.offerPriceType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have offerQAPRate := readOptional_part [57, 54, 54, 51] record.offerQAPRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have offerAutoEx := readOptional_part [57, 54, 56, 49] record.offerAutoEx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have lockCrossFlag := readOptional_part [57, 53, 48, 54] record.lockCrossFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have unsolicited := readOptional_part [57, 53, 51, 52] record.unsolicited tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have nonAffiliate := readOptional_part [57, 53, 51, 53] record.nonAffiliate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have cancelTime := readOptional_part [57, 53, 57, 54] record.cancelTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have autoCancelEOD := readOptional_part [57, 53, 57, 55] record.autoCancelEOD tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  simp only [Quote.decode, msgRefID, updateType, symbol, symbolSfx, securityID, iDSource, aTSOnly, cATroutedQuoteID, bidPriceType, bidPx, bidSize, bidQAPRate, bidAutoEx, offerPriceType, offerPx, offerSize, offerQAPRate, offerAutoEx, lockCrossFlag, unsolicited, nonAffiliate, cancelTime, autoCancelEOD, some_bind] <;> rfl

structure QuoteCancel where
  msgRefID : Option (Terminated 1)  -- tag 9670
  symbol : Option (Terminated 1)  -- tag 55
  symbolSfx : Option (Terminated 1)  -- tag 65
  securityID : Option (Terminated 1)  -- tag 48
  iDSource : Option (Terminated 1)  -- tag 22

def QuoteCancel.parts (record : QuoteCancel) : List Part :=
  [Part.optional [57, 54, 55, 48] record.msgRefID,
   Part.optional [53, 53] record.symbol,
   Part.optional [54, 53] record.symbolSfx,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.iDSource]

def QuoteCancel.tags : List (List (List UInt8)) :=
  [[[57, 54, 55, 48]], [[53, 53]], [[54, 53]], [[52, 56]], [[50, 50]]]

theorem QuoteCancel.shape (record : QuoteCancel) : record.parts.map Part.tags = QuoteCancel.tags := rfl

def QuoteCancel.decode (tokens : List Token) : Option QuoteCancel := do
  let msgRefID ← readOptional [57, 54, 55, 48] tokens
  let symbol ← readOptional [53, 53] tokens
  let symbolSfx ← readOptional [54, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let iDSource ← readOptional [50, 50] tokens
  pure { msgRefID, symbol, symbolSfx, securityID, iDSource }

theorem QuoteCancel.decode_agrees (record : QuoteCancel) (tokens : List Token)
    (agrees : ∀ tags ∈ QuoteCancel.tags, select tags tokens = select tags (encodeParts record.parts)) :
    QuoteCancel.decode tokens = some record := by
  have distinct : QuoteCancel.tags.flatten.Nodup := by decide +kernel
  have msgRefID := readOptional_part [57, 54, 55, 48] record.msgRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readOptional_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbolSfx := readOptional_part [54, 53] record.symbolSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have iDSource := readOptional_part [50, 50] record.iDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [QuoteCancel.decode, msgRefID, symbol, symbolSfx, securityID, iDSource, some_bind] <;> rfl

structure TraderState where
  msgRefID : Option (Terminated 1)  -- tag 9670
  openCloseState : Terminated 1  -- tag 9671

def TraderState.parts (record : TraderState) : List Part :=
  [Part.optional [57, 54, 55, 48] record.msgRefID,
   Part.required [57, 54, 55, 49] record.openCloseState]

def TraderState.tags : List (List (List UInt8)) :=
  [[[57, 54, 55, 48]], [[57, 54, 55, 49]]]

theorem TraderState.shape (record : TraderState) : record.parts.map Part.tags = TraderState.tags := rfl

def TraderState.decode (tokens : List Token) : Option TraderState := do
  let msgRefID ← readOptional [57, 54, 55, 48] tokens
  let openCloseState ← readRequired [57, 54, 55, 49] tokens
  pure { msgRefID, openCloseState }

theorem TraderState.decode_agrees (record : TraderState) (tokens : List Token)
    (agrees : ∀ tags ∈ TraderState.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TraderState.decode tokens = some record := by
  have distinct : TraderState.tags.flatten.Nodup := by decide +kernel
  have msgRefID := readOptional_part [57, 54, 55, 48] record.msgRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have openCloseState := readRequired_part [57, 54, 55, 49] record.openCloseState tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [TraderState.decode, msgRefID, openCloseState, some_bind] <;> rfl

inductive Message where
  | quote (header : Header) (r0 : Quote)
  | quoteCancel (header : Header) (r0 : QuoteCancel)
  | traderState (header : Header) (r0 : TraderState)

def Message.tokens : Message → List Token
  | .quote header r0 => ⟨[51, 53], ⟨[83], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quoteCancel header r0 => ⟨[51, 53], ⟨[90], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)
  | .traderState header r0 => ⟨[51, 53], ⟨[79, 84], by decide⟩⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value.val = [83] then
        if known (Header.tags ++ Quote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Quote.decode rest
          pure (.quote header r0)
        else none
      else if token.value.val = [90] then
        if known (Header.tags ++ QuoteCancel.tags) rest then do
          let header ← Header.decode rest
          let r0 ← QuoteCancel.decode rest
          pure (.quoteCancel header r0)
        else none
      else if token.value.val = [79, 84] then
        if known (Header.tags ++ TraderState.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TraderState.decode rest
          pure (.traderState header r0)
        else none
      else none
    else none

theorem Message.decode_quote (header : Header) (r0 : Quote) :
    Message.decode (Message.tokens (.quote header r0)) = some (.quote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) rfl rfl (by decide +kernel))
  have c1 := Quote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Quote.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decode (Message.tokens (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) rfl rfl (by decide +kernel))
  have c1 := QuoteCancel.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (QuoteCancel.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ QuoteCancel.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_traderState (header : Header) (r0 : TraderState) :
    Message.decode (Message.tokens (.traderState header r0)) = some (.traderState header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TraderState.tags) rfl rfl (by decide +kernel))
  have c1 := TraderState.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TraderState.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TraderState.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | quote header r0 => exact Message.decode_quote header r0
  | quoteCancel header r0 => exact Message.decode_quoteCancel header r0
  | traderState header r0 => exact Message.decode_traderState header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_quote (header : Header) (r0 : Quote) :
    Message.decodeBytes (Message.encode (.quote header r0)) = some (.quote header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[83], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ Quote.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quote header r0

theorem Message.decodeBytes_quoteCancel (header : Header) (r0 : QuoteCancel) :
    Message.decodeBytes (Message.encode (.quoteCancel header r0)) = some (.quoteCancel header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[90], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ QuoteCancel.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quoteCancel header r0

theorem Message.decodeBytes_traderState (header : Header) (r0 : TraderState) :
    Message.decodeBytes (Message.encode (.traderState header r0)) = some (.traderState header r0) := by
  have tokens := decodeTokens_message ⟨[51, 53], ⟨[79, 84], by decide⟩⟩ (header.parts ++ r0.parts) (Header.tags ++ TraderState.tags)
    rfl (by decide +kernel) (by decide +kernel)
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_traderState header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | quote header r0 => exact Message.decodeBytes_quote header r0
  | quoteCancel header r0 => exact Message.decodeBytes_quoteCancel header r0
  | traderState header r0 => exact Message.decodeBytes_traderState header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.OtcmarketsLinkatsQuotationFixV17Client
