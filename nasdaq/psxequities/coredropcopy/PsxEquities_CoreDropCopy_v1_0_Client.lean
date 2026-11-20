import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v1.0, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqPsxequitiesCoredropcopyFixV10Client

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  possDupFlag : Option (Terminated 1)  -- tag 43
  msgSeqNum : Terminated 1  -- tag 34
  sendingTime : Terminated 1  -- tag 52
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [51, 52] record.msgSeqNum,
   Part.required [53, 50] record.sendingTime,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[52, 57]], [[53, 54]], [[52, 51]], [[51, 52]], [[53, 50]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let msgSeqNum ← readRequired [51, 52] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { senderCompID, targetCompID, possDupFlag, msgSeqNum, sendingTime, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Header.decode, senderCompID, targetCompID, possDupFlag, msgSeqNum, sendingTime, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
        (paired_none pairing))))))

structure Logon where
  encryptMethod : Option (Terminated 1)  -- tag 98
  heartBtInt : Terminated 1  -- tag 108

def Logon.parts (record : Logon) : List Part :=
  [Part.optional [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readOptional [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  pure { encryptMethod, heartBtInt }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readOptional_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_none pairing))

structure Heartbeat

def Heartbeat.parts (_ : Heartbeat) : List Part :=
  []

def Heartbeat.tags : List (List (List UInt8)) :=
  []

theorem Heartbeat.shape (record : Heartbeat) : record.parts.map Part.tags = Heartbeat.tags := rfl

def Heartbeat.decode (_ : List Token) : Option Heartbeat := some {}

theorem Heartbeat.decode_agrees (record : Heartbeat) (tokens : List Token)
    (_ : ∀ tags ∈ Heartbeat.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Heartbeat.decode tokens = some record := by
  rfl

theorem Heartbeat.taken (record : Heartbeat) : Paired pairing (encodeParts record.parts) :=
  paired_none pairing

inductive Message where
  | logon (header : Header) (r0 : Logon)
  | heartbeat (header : Header) (r0 : Heartbeat)

def Message.tokens : Message → List Token
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [65] then
        if known (Header.tags ++ Logon.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Logon.decode rest
          pure (.logon header r0)
        else none
      else if token.value = [48] then
        if known (Header.tags ++ Heartbeat.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Heartbeat.decode rest
          pure (.heartbeat header r0)
        else none
      else none
    else none

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | logon header r0 => exact Message.decode_logon header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_logon (header : Header) (r0 : Logon) :
    Message.decodeBytes (Message.encode (.logon header r0)) = some (.logon header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [65]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Logon.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_logon header r0

theorem Message.decodeBytes_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decodeBytes (Message.encode (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [48]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Heartbeat.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_heartbeat header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0

/-- BeginString as the venue states it: one of FIX.4.0, FIX.4.1, FIX.4.2, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 48], [70, 73, 88, 46, 52, 46, 49], [70, 73, 88, 46, 52, 46, 50]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.NasdaqPsxequitiesCoredropcopyFixV10Client
