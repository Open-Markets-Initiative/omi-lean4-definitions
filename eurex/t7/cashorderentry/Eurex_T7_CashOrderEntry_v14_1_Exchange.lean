import Wire

/-!
# Eurex Exchange Cash Order Entry v14.1, Exchange messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.EurexT7CashorderentryFixV141Exchange

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 50]], [[53, 54]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, sendingTime, targetCompID, possResend, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
         (paired_none pairing)))))))

structure BusinessMessageAck where
  refSeqNum : Terminated 1  -- tag 45
  refMsgType : Terminated 1  -- tag 372
  businessAckRefID : Terminated 1  -- tag 30379

def BusinessMessageAck.parts (record : BusinessMessageAck) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 48, 51, 55, 57] record.businessAckRefID]

def BusinessMessageAck.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[51, 55, 50]], [[51, 48, 51, 55, 57]]]

theorem BusinessMessageAck.shape (record : BusinessMessageAck) : record.parts.map Part.tags = BusinessMessageAck.tags := rfl

def BusinessMessageAck.decode (tokens : List Token) : Option BusinessMessageAck := do
  let refSeqNum ← readRequired [52, 53] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessAckRefID ← readRequired [51, 48, 51, 55, 57] tokens
  pure { refSeqNum, refMsgType, businessAckRefID }

theorem BusinessMessageAck.decode_agrees (record : BusinessMessageAck) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageAck.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageAck.decode tokens = some record := by
  have distinct : BusinessMessageAck.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have businessAckRefID := readRequired_part [51, 48, 51, 55, 57] record.businessAckRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [BusinessMessageAck.decode, refSeqNum, refMsgType, businessAckRefID, some_bind] <;> rfl

theorem BusinessMessageAck.taken (record : BusinessMessageAck) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 48, 51, 55, 57] record.businessAckRefID (by decide) (by decide))
     (paired_none pairing)))

structure BusinessMessageReject where
  refSeqNum : Option (Terminated 1)  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refMsgType : Terminated 1  -- tag 372
  businessRejectReason : Terminated 1  -- tag 380
  businessRejectRefID : Option (Terminated 1)  -- tag 379

def BusinessMessageReject.parts (record : BusinessMessageReject) : List Part :=
  [Part.optional [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.required [51, 55, 50] record.refMsgType,
   Part.required [51, 56, 48] record.businessRejectReason,
   Part.optional [51, 55, 57] record.businessRejectRefID]

def BusinessMessageReject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 50]], [[51, 56, 48]], [[51, 55, 57]]]

theorem BusinessMessageReject.shape (record : BusinessMessageReject) : record.parts.map Part.tags = BusinessMessageReject.tags := rfl

def BusinessMessageReject.decode (tokens : List Token) : Option BusinessMessageReject := do
  let refSeqNum ← readOptional [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let businessRejectReason ← readRequired [51, 56, 48] tokens
  let businessRejectRefID ← readOptional [51, 55, 57] tokens
  pure { refSeqNum, text, refMsgType, businessRejectReason, businessRejectRefID }

theorem BusinessMessageReject.decode_agrees (record : BusinessMessageReject) (tokens : List Token)
    (agrees : ∀ tags ∈ BusinessMessageReject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    BusinessMessageReject.decode tokens = some record := by
  have distinct : BusinessMessageReject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readOptional_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have businessRejectReason := readRequired_part [51, 56, 48] record.businessRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have businessRejectRefID := readOptional_part [51, 55, 57] record.businessRejectRefID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [BusinessMessageReject.decode, refSeqNum, text, refMsgType, businessRejectReason, businessRejectRefID, some_bind] <;> rfl

theorem BusinessMessageReject.taken (record : BusinessMessageReject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56, 48] record.businessRejectReason (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55, 57] record.businessRejectRefID (by decide) (by decide))
       (paired_none pairing)))))

structure NoPartyIDs where
  partyID : Terminated 1  -- tag 448
  partyIDSource : Terminated 1  -- tag 447
  partyRole : Terminated 1  -- tag 452
  partyRoleQualifier : Option (Terminated 1)  -- tag 2376
  noPartySubIDs : Option (Terminated 1)  -- tag 802
  partySubID : Option (Terminated 1)  -- tag 523
  partySubIDType : Option (Terminated 1)  -- tag 803

def NoPartyIDs.parts (record : NoPartyIDs) : List Part :=
  [Part.required [52, 52, 56] record.partyID,
   Part.required [52, 52, 55] record.partyIDSource,
   Part.required [52, 53, 50] record.partyRole,
   Part.optional [50, 51, 55, 54] record.partyRoleQualifier,
   Part.optional [56, 48, 50] record.noPartySubIDs,
   Part.optional [53, 50, 51] record.partySubID,
   Part.optional [56, 48, 51] record.partySubIDType]

def NoPartyIDs.tags : List (List (List UInt8)) :=
  [[[52, 52, 56]], [[52, 52, 55]], [[52, 53, 50]], [[50, 51, 55, 54]], [[56, 48, 50]], [[53, 50, 51]], [[56, 48, 51]]]

theorem NoPartyIDs.shape (record : NoPartyIDs) : record.parts.map Part.tags = NoPartyIDs.tags := rfl

def NoPartyIDs.decode (tokens : List Token) : Option NoPartyIDs := do
  let partyID ← readRequired [52, 52, 56] tokens
  let partyIDSource ← readRequired [52, 52, 55] tokens
  let partyRole ← readRequired [52, 53, 50] tokens
  let partyRoleQualifier ← readOptional [50, 51, 55, 54] tokens
  let noPartySubIDs ← readOptional [56, 48, 50] tokens
  let partySubID ← readOptional [53, 50, 51] tokens
  let partySubIDType ← readOptional [56, 48, 51] tokens
  pure { partyID, partyIDSource, partyRole, partyRoleQualifier, noPartySubIDs, partySubID, partySubIDType }

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
  have partyRoleQualifier := readOptional_part [50, 51, 55, 54] record.partyRoleQualifier tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noPartySubIDs := readOptional_part [56, 48, 50] record.noPartySubIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partySubID := readOptional_part [53, 50, 51] record.partySubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have partySubIDType := readOptional_part [56, 48, 51] record.partySubIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [NoPartyIDs.decode, partyID, partyIDSource, partyRole, partyRoleQualifier, noPartySubIDs, partySubID, partySubIDType, some_bind] <;> rfl

theorem NoPartyIDs.taken (record : NoPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 52, 56] record.partyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 52, 55] record.partyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 53, 50] record.partyRole (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 51, 55, 54] record.partyRoleQualifier (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50] record.noPartySubIDs (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 50, 51] record.partySubID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [56, 48, 51] record.partySubIDType (by decide) (by decide))
         (paired_none pairing)))))))

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

structure NoSecurityAltID where
  securityAltID : Terminated 1  -- tag 455
  securityAltIDSource : Terminated 1  -- tag 456

def NoSecurityAltID.parts (record : NoSecurityAltID) : List Part :=
  [Part.required [52, 53, 53] record.securityAltID,
   Part.required [52, 53, 54] record.securityAltIDSource]

def NoSecurityAltID.tags : List (List (List UInt8)) :=
  [[[52, 53, 53]], [[52, 53, 54]]]

theorem NoSecurityAltID.shape (record : NoSecurityAltID) : record.parts.map Part.tags = NoSecurityAltID.tags := rfl

def NoSecurityAltID.decode (tokens : List Token) : Option NoSecurityAltID := do
  let securityAltID ← readRequired [52, 53, 53] tokens
  let securityAltIDSource ← readRequired [52, 53, 54] tokens
  pure { securityAltID, securityAltIDSource }

theorem NoSecurityAltID.decode_agrees (record : NoSecurityAltID) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSecurityAltID.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSecurityAltID.decode tokens = some record := by
  have distinct : NoSecurityAltID.tags.flatten.Nodup := by decide +kernel
  have securityAltID := readRequired_part [52, 53, 53] record.securityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityAltIDSource := readRequired_part [52, 53, 54] record.securityAltIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoSecurityAltID.decode, securityAltID, securityAltIDSource, some_bind] <;> rfl

theorem NoSecurityAltID.taken (record : NoSecurityAltID) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53, 53] record.securityAltID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 53, 54] record.securityAltIDSource (by decide) (by decide))
    (paired_none pairing))

def NoSecurityAltID.members : List (List UInt8) := NoSecurityAltID.tags.flatten

def NoSecurityAltID.encode (entry : NoSecurityAltID) : List Token := encodeParts entry.parts

theorem NoSecurityAltID.decode_encode (entry : NoSecurityAltID) : NoSecurityAltID.decode entry.encode = some entry :=
  NoSecurityAltID.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSecurityAltID.within (entry : NoSecurityAltID) : ∀ token ∈ entry.encode, token.tag ∈ NoSecurityAltID.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSecurityAltID.shape] at this

theorem NoSecurityAltID.led (entry : NoSecurityAltID) : Lead [52, 53, 53] entry.encode :=
  lead_parts [52, 53, 53] entry.securityAltID _ NoSecurityAltID.tags.tail rfl (by decide +kernel)

structure NoMatchInst where
  matchInst : Terminated 1  -- tag 1625
  matchInstCrossID : Terminated 1  -- tag 28744

def NoMatchInst.parts (record : NoMatchInst) : List Part :=
  [Part.required [49, 54, 50, 53] record.matchInst,
   Part.required [50, 56, 55, 52, 52] record.matchInstCrossID]

def NoMatchInst.tags : List (List (List UInt8)) :=
  [[[49, 54, 50, 53]], [[50, 56, 55, 52, 52]]]

theorem NoMatchInst.shape (record : NoMatchInst) : record.parts.map Part.tags = NoMatchInst.tags := rfl

def NoMatchInst.decode (tokens : List Token) : Option NoMatchInst := do
  let matchInst ← readRequired [49, 54, 50, 53] tokens
  let matchInstCrossID ← readRequired [50, 56, 55, 52, 52] tokens
  pure { matchInst, matchInstCrossID }

theorem NoMatchInst.decode_agrees (record : NoMatchInst) (tokens : List Token)
    (agrees : ∀ tags ∈ NoMatchInst.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoMatchInst.decode tokens = some record := by
  have distinct : NoMatchInst.tags.flatten.Nodup := by decide +kernel
  have matchInst := readRequired_part [49, 54, 50, 53] record.matchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have matchInstCrossID := readRequired_part [50, 56, 55, 52, 52] record.matchInstCrossID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoMatchInst.decode, matchInst, matchInstCrossID, some_bind] <;> rfl

theorem NoMatchInst.taken (record : NoMatchInst) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 50, 53] record.matchInst (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 52, 52] record.matchInstCrossID (by decide) (by decide))
    (paired_none pairing))

def NoMatchInst.members : List (List UInt8) := NoMatchInst.tags.flatten

def NoMatchInst.encode (entry : NoMatchInst) : List Token := encodeParts entry.parts

theorem NoMatchInst.decode_encode (entry : NoMatchInst) : NoMatchInst.decode entry.encode = some entry :=
  NoMatchInst.decode_agrees entry _ (fun _ _ => rfl)

theorem NoMatchInst.within (entry : NoMatchInst) : ∀ token ∈ entry.encode, token.tag ∈ NoMatchInst.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoMatchInst.shape] at this

theorem NoMatchInst.led (entry : NoMatchInst) : Lead [49, 54, 50, 53] entry.encode :=
  lead_parts [49, 54, 50, 53] entry.matchInst _ NoMatchInst.tags.tail rfl (by decide +kernel)

structure NoOrderEvents where
  orderEventType : Terminated 1  -- tag 1796

def NoOrderEvents.parts (record : NoOrderEvents) : List Part :=
  [Part.required [49, 55, 57, 54] record.orderEventType]

def NoOrderEvents.tags : List (List (List UInt8)) :=
  [[[49, 55, 57, 54]]]

theorem NoOrderEvents.shape (record : NoOrderEvents) : record.parts.map Part.tags = NoOrderEvents.tags := rfl

def NoOrderEvents.decode (tokens : List Token) : Option NoOrderEvents := do
  let orderEventType ← readRequired [49, 55, 57, 54] tokens
  pure { orderEventType }

theorem NoOrderEvents.decode_agrees (record : NoOrderEvents) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderEvents.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderEvents.decode tokens = some record := by
  have distinct : NoOrderEvents.tags.flatten.Nodup := by decide +kernel
  have orderEventType := readRequired_part [49, 55, 57, 54] record.orderEventType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoOrderEvents.decode, orderEventType, some_bind] <;> rfl

theorem NoOrderEvents.taken (record : NoOrderEvents) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 55, 57, 54] record.orderEventType (by decide) (by decide))
   (paired_none pairing)

def NoOrderEvents.members : List (List UInt8) := NoOrderEvents.tags.flatten

def NoOrderEvents.encode (entry : NoOrderEvents) : List Token := encodeParts entry.parts

theorem NoOrderEvents.decode_encode (entry : NoOrderEvents) : NoOrderEvents.decode entry.encode = some entry :=
  NoOrderEvents.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrderEvents.within (entry : NoOrderEvents) : ∀ token ∈ entry.encode, token.tag ∈ NoOrderEvents.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrderEvents.shape] at this

theorem NoOrderEvents.led (entry : NoOrderEvents) : Lead [49, 55, 57, 54] entry.encode :=
  lead_parts [49, 55, 57, 54] entry.orderEventType _ NoOrderEvents.tags.tail rfl (by decide +kernel)

structure ExecutionReport where
  noPartyIDs : List NoPartyIDs  -- tag 453
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  pegOffsetValue : Option (Terminated 1)  -- tag 211
  pegOffsetType : Option (Terminated 1)  -- tag 836
  noMatchInst : List NoMatchInst  -- tag 1624
  displayQty : Option (Terminated 1)  -- tag 1138
  displayMethod : Option (Terminated 1)  -- tag 1084
  displayLowQty : Option (Terminated 1)  -- tag 1085
  displayHighQty : Option (Terminated 1)  -- tag 1086
  noOrderEvents : List NoOrderEvents  -- tag 1795
  clOrdID : Option (Terminated 1)  -- tag 11
  currency : Option (Terminated 1)  -- tag 15
  cumQty : Terminated 1  -- tag 14
  execID : Terminated 1  -- tag 17
  execInst : Option (Terminated 1)  -- tag 18
  lastPx : Option (Terminated 1)  -- tag 31
  lastQty : Option (Terminated 1)  -- tag 32
  orderID : Terminated 1  -- tag 37
  orderQty : Terminated 1  -- tag 38
  minQty : Option (Terminated 1)  -- tag 110
  ordStatus : Terminated 1  -- tag 39
  ordType : Option (Terminated 1)  -- tag 40
  midPointType : Option (Terminated 1)  -- tag 30388
  origClOrdID : Option (Terminated 1)  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  freeText1 : Option (Terminated 1)  -- tag 25007
  timeInForce : Option (Terminated 1)  -- tag 59
  stopPx : Option (Terminated 1)  -- tag 99
  execType : Terminated 1  -- tag 150
  leavesQty : Terminated 1  -- tag 151
  brokerInternalizationID : Option (Terminated 1)  -- tag 25263
  tradingSessionID : Option (Terminated 1)  -- tag 336
  execRestatementReason : Option (Terminated 1)  -- tag 378
  expireDate : Option (Terminated 1)  -- tag 432
  secondaryExecID : Option (Terminated 1)  -- tag 527
  matchType : Option (Terminated 1)  -- tag 574
  tradingSessionSubID : Option (Terminated 1)  -- tag 625
  lastLiquidityInd : Option (Terminated 1)  -- tag 851
  trdMatchID : Option (Terminated 1)  -- tag 880
  refOrderID : Option (Terminated 1)  -- tag 1080
  refOrderIDSource : Option (Terminated 1)  -- tag 1081
  tradingCapacity : Option (Terminated 1)  -- tag 1815
  crossedIndicator : Option (Terminated 1)  -- tag 2523
  triggered : Option (Terminated 1)  -- tag 1823
  bBOSetting : Option (Terminated 1)  -- tag 25245
  freeText2 : Option (Terminated 1)  -- tag 25008
  freeText4 : Option (Terminated 1)  -- tag 25107
  uTransactTime : Option (Terminated 1)  -- tag 30060
  orderIDSfx : Option (Terminated 1)  -- tag 25108
  tradeAtCloseOptIn : Option (Terminated 1)  -- tag 30625

def ExecutionReport.parts (record : ExecutionReport) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.optional [50, 49, 49] record.pegOffsetValue,
   Part.optional [56, 51, 54] record.pegOffsetType,
   Part.group [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within record.noMatchInst,
   Part.optional [49, 49, 51, 56] record.displayQty,
   Part.optional [49, 48, 56, 52] record.displayMethod,
   Part.optional [49, 48, 56, 53] record.displayLowQty,
   Part.optional [49, 48, 56, 54] record.displayHighQty,
   Part.group [49, 55, 57, 53] NoOrderEvents.members NoOrderEvents.encode NoOrderEvents.within record.noOrderEvents,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [49, 53] record.currency,
   Part.required [49, 52] record.cumQty,
   Part.required [49, 55] record.execID,
   Part.optional [49, 56] record.execInst,
   Part.optional [51, 49] record.lastPx,
   Part.optional [51, 50] record.lastQty,
   Part.required [51, 55] record.orderID,
   Part.required [51, 56] record.orderQty,
   Part.optional [49, 49, 48] record.minQty,
   Part.required [51, 57] record.ordStatus,
   Part.optional [52, 48] record.ordType,
   Part.optional [51, 48, 51, 56, 56] record.midPointType,
   Part.optional [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.optional [50, 53, 48, 48, 55] record.freeText1,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [57, 57] record.stopPx,
   Part.required [49, 53, 48] record.execType,
   Part.required [49, 53, 49] record.leavesQty,
   Part.optional [50, 53, 50, 54, 51] record.brokerInternalizationID,
   Part.optional [51, 51, 54] record.tradingSessionID,
   Part.optional [51, 55, 56] record.execRestatementReason,
   Part.optional [52, 51, 50] record.expireDate,
   Part.optional [53, 50, 55] record.secondaryExecID,
   Part.optional [53, 55, 52] record.matchType,
   Part.optional [54, 50, 53] record.tradingSessionSubID,
   Part.optional [56, 53, 49] record.lastLiquidityInd,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.optional [49, 48, 56, 48] record.refOrderID,
   Part.optional [49, 48, 56, 49] record.refOrderIDSource,
   Part.optional [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [50, 53, 50, 51] record.crossedIndicator,
   Part.optional [49, 56, 50, 51] record.triggered,
   Part.optional [50, 53, 50, 52, 53] record.bBOSetting,
   Part.optional [50, 53, 48, 48, 56] record.freeText2,
   Part.optional [50, 53, 49, 48, 55] record.freeText4,
   Part.optional [51, 48, 48, 54, 48] record.uTransactTime,
   Part.optional [50, 53, 49, 48, 56] record.orderIDSfx,
   Part.optional [51, 48, 54, 50, 53] record.tradeAtCloseOptIn]

def ExecutionReport.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[50, 49, 49]], [[56, 51, 54]], [49, 54, 50, 52] :: NoMatchInst.members, [[49, 49, 51, 56]], [[49, 48, 56, 52]], [[49, 48, 56, 53]], [[49, 48, 56, 54]], [49, 55, 57, 53] :: NoOrderEvents.members, [[49, 49]], [[49, 53]], [[49, 52]], [[49, 55]], [[49, 56]], [[51, 49]], [[51, 50]], [[51, 55]], [[51, 56]], [[49, 49, 48]], [[51, 57]], [[52, 48]], [[51, 48, 51, 56, 56]], [[52, 49]], [[52, 52]], [[53, 52]], [[50, 53, 48, 48, 55]], [[53, 57]], [[57, 57]], [[49, 53, 48]], [[49, 53, 49]], [[50, 53, 50, 54, 51]], [[51, 51, 54]], [[51, 55, 56]], [[52, 51, 50]], [[53, 50, 55]], [[53, 55, 52]], [[54, 50, 53]], [[56, 53, 49]], [[56, 56, 48]], [[49, 48, 56, 48]], [[49, 48, 56, 49]], [[49, 56, 49, 53]], [[50, 53, 50, 51]], [[49, 56, 50, 51]], [[50, 53, 50, 52, 53]], [[50, 53, 48, 48, 56]], [[50, 53, 49, 48, 55]], [[51, 48, 48, 54, 48]], [[50, 53, 49, 48, 56]], [[51, 48, 54, 50, 53]]]

theorem ExecutionReport.shape (record : ExecutionReport) : record.parts.map Part.tags = ExecutionReport.tags := rfl

def ExecutionReport.decode (tokens : List Token) : Option ExecutionReport := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let pegOffsetValue ← readOptional [50, 49, 49] tokens
  let pegOffsetType ← readOptional [56, 51, 54] tokens
  let noMatchInst ← readGroup [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.decode tokens
  let displayQty ← readOptional [49, 49, 51, 56] tokens
  let displayMethod ← readOptional [49, 48, 56, 52] tokens
  let displayLowQty ← readOptional [49, 48, 56, 53] tokens
  let displayHighQty ← readOptional [49, 48, 56, 54] tokens
  let noOrderEvents ← readGroup [49, 55, 57, 53] [49, 55, 57, 54] NoOrderEvents.members NoOrderEvents.decode tokens
  let clOrdID ← readOptional [49, 49] tokens
  let currency ← readOptional [49, 53] tokens
  let cumQty ← readRequired [49, 52] tokens
  let execID ← readRequired [49, 55] tokens
  let execInst ← readOptional [49, 56] tokens
  let lastPx ← readOptional [51, 49] tokens
  let lastQty ← readOptional [51, 50] tokens
  let orderID ← readRequired [51, 55] tokens
  let orderQty ← readRequired [51, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let ordStatus ← readRequired [51, 57] tokens
  let ordType ← readOptional [52, 48] tokens
  let midPointType ← readOptional [51, 48, 51, 56, 56] tokens
  let origClOrdID ← readOptional [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let freeText1 ← readOptional [50, 53, 48, 48, 55] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let stopPx ← readOptional [57, 57] tokens
  let execType ← readRequired [49, 53, 48] tokens
  let leavesQty ← readRequired [49, 53, 49] tokens
  let brokerInternalizationID ← readOptional [50, 53, 50, 54, 51] tokens
  let tradingSessionID ← readOptional [51, 51, 54] tokens
  let execRestatementReason ← readOptional [51, 55, 56] tokens
  let expireDate ← readOptional [52, 51, 50] tokens
  let secondaryExecID ← readOptional [53, 50, 55] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let tradingSessionSubID ← readOptional [54, 50, 53] tokens
  let lastLiquidityInd ← readOptional [56, 53, 49] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let refOrderID ← readOptional [49, 48, 56, 48] tokens
  let refOrderIDSource ← readOptional [49, 48, 56, 49] tokens
  let tradingCapacity ← readOptional [49, 56, 49, 53] tokens
  let crossedIndicator ← readOptional [50, 53, 50, 51] tokens
  let triggered ← readOptional [49, 56, 50, 51] tokens
  let bBOSetting ← readOptional [50, 53, 50, 52, 53] tokens
  let freeText2 ← readOptional [50, 53, 48, 48, 56] tokens
  let freeText4 ← readOptional [50, 53, 49, 48, 55] tokens
  let uTransactTime ← readOptional [51, 48, 48, 54, 48] tokens
  let orderIDSfx ← readOptional [50, 53, 49, 48, 56] tokens
  let tradeAtCloseOptIn ← readOptional [51, 48, 54, 50, 53] tokens
  pure { noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderEvents, clOrdID, currency, cumQty, execID, execInst, lastPx, lastQty, orderID, orderQty, minQty, ordStatus, ordType, midPointType, origClOrdID, price, side, freeText1, timeInForce, stopPx, execType, leavesQty, brokerInternalizationID, tradingSessionID, execRestatementReason, expireDate, secondaryExecID, matchType, tradingSessionSubID, lastLiquidityInd, trdMatchID, refOrderID, refOrderIDSource, tradingCapacity, crossedIndicator, triggered, bBOSetting, freeText2, freeText4, uTransactTime, orderIDSfx, tradeAtCloseOptIn }

theorem ExecutionReport.decode_agrees (record : ExecutionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ ExecutionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    ExecutionReport.decode tokens = some record := by
  have distinct : ExecutionReport.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have pegOffsetValue := readOptional_part [50, 49, 49] record.pegOffsetValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have pegOffsetType := readOptional_part [56, 51, 54] record.pegOffsetType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noMatchInst := readGroup_part [49, 54, 50, 52] [49, 54, 50, 53] NoMatchInst.members NoMatchInst.encode NoMatchInst.within NoMatchInst.decode NoMatchInst.decode_encode NoMatchInst.led record.noMatchInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have displayQty := readOptional_part [49, 49, 51, 56] record.displayQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have displayMethod := readOptional_part [49, 48, 56, 52] record.displayMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have displayLowQty := readOptional_part [49, 48, 56, 53] record.displayLowQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have displayHighQty := readOptional_part [49, 48, 56, 54] record.displayHighQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have noOrderEvents := readGroup_part [49, 55, 57, 53] [49, 55, 57, 54] NoOrderEvents.members NoOrderEvents.encode NoOrderEvents.within NoOrderEvents.decode NoOrderEvents.decode_encode NoOrderEvents.led record.noOrderEvents tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have cumQty := readRequired_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have execID := readRequired_part [49, 55] record.execID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have lastPx := readOptional_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have lastQty := readOptional_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have orderID := readRequired_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have ordStatus := readRequired_part [51, 57] record.ordStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have midPointType := readOptional_part [51, 48, 51, 56, 56] record.midPointType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have origClOrdID := readOptional_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have freeText1 := readOptional_part [50, 53, 48, 48, 55] record.freeText1 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have stopPx := readOptional_part [57, 57] record.stopPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have execType := readRequired_part [49, 53, 48] record.execType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have leavesQty := readRequired_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have brokerInternalizationID := readOptional_part [50, 53, 50, 54, 51] record.brokerInternalizationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have tradingSessionID := readOptional_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  have execRestatementReason := readOptional_part [51, 55, 56] record.execRestatementReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 40 (by decide +kernel)))
  have expireDate := readOptional_part [52, 51, 50] record.expireDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 41 (by decide +kernel)))
  have secondaryExecID := readOptional_part [53, 50, 55] record.secondaryExecID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 42 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 43 (by decide +kernel)))
  have tradingSessionSubID := readOptional_part [54, 50, 53] record.tradingSessionSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 44 (by decide +kernel)))
  have lastLiquidityInd := readOptional_part [56, 53, 49] record.lastLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 45 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 46 (by decide +kernel)))
  have refOrderID := readOptional_part [49, 48, 56, 48] record.refOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 47 (by decide +kernel)))
  have refOrderIDSource := readOptional_part [49, 48, 56, 49] record.refOrderIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 48 (by decide +kernel)))
  have tradingCapacity := readOptional_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 49 (by decide +kernel)))
  have crossedIndicator := readOptional_part [50, 53, 50, 51] record.crossedIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 50 (by decide +kernel)))
  have triggered := readOptional_part [49, 56, 50, 51] record.triggered tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 51 (by decide +kernel)))
  have bBOSetting := readOptional_part [50, 53, 50, 52, 53] record.bBOSetting tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 52 (by decide +kernel)))
  have freeText2 := readOptional_part [50, 53, 48, 48, 56] record.freeText2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 53 (by decide +kernel)))
  have freeText4 := readOptional_part [50, 53, 49, 48, 55] record.freeText4 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 54 (by decide +kernel)))
  have uTransactTime := readOptional_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 55 (by decide +kernel)))
  have orderIDSfx := readOptional_part [50, 53, 49, 48, 56] record.orderIDSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 56 (by decide +kernel)))
  have tradeAtCloseOptIn := readOptional_part [51, 48, 54, 50, 53] record.tradeAtCloseOptIn tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 57 (by decide +kernel)))
  simp only [ExecutionReport.decode, noPartyIDs, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, pegOffsetValue, pegOffsetType, noMatchInst, displayQty, displayMethod, displayLowQty, displayHighQty, noOrderEvents, clOrdID, currency, cumQty, execID, execInst, lastPx, lastQty, orderID, orderQty, minQty, ordStatus, ordType, midPointType, origClOrdID, price, side, freeText1, timeInForce, stopPx, execType, leavesQty, brokerInternalizationID, tradingSessionID, execRestatementReason, expireDate, secondaryExecID, matchType, tradingSessionSubID, lastLiquidityInd, trdMatchID, refOrderID, refOrderIDSource, tradingCapacity, crossedIndicator, triggered, bBOSetting, freeText2, freeText4, uTransactTime, orderIDSfx, tradeAtCloseOptIn, some_bind] <;> rfl

theorem ExecutionReport.taken (record : ExecutionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within (by decide) (by decide) NoSecurityAltID.taken record.noSecurityAltID)
       (paired_cons pairing _ _ (paired_optional pairing [50, 50, 51] record.couponRate (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 48] record.deliveryType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegOffsetValue (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [56, 51, 54] record.pegOffsetType (by decide) (by decide))
             (paired_cons pairing _ _ (paired_group pairing [49, 54, 50, 52] NoMatchInst.members NoMatchInst.encode NoMatchInst.within (by decide) (by decide) NoMatchInst.taken record.noMatchInst)
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 51, 56] record.displayQty (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 52] record.displayMethod (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 53] record.displayLowQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 54] record.displayHighQty (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_group pairing [49, 55, 57, 53] NoOrderEvents.members NoOrderEvents.encode NoOrderEvents.within (by decide) (by decide) NoOrderEvents.taken record.noOrderEvents)
                   (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [49, 52] record.cumQty (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [49, 55] record.execID (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [51, 49] record.lastPx (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [51, 50] record.lastQty (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_required pairing [51, 55] record.orderID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_required pairing [51, 57] record.ordStatus (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [51, 48, 51, 56, 56] record.midPointType (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [52, 49] record.origClOrdID (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 48, 55] record.freeText1 (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [57, 57] record.stopPx (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_required pairing [49, 53, 48] record.execType (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_required pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 53, 50, 54, 51] record.brokerInternalizationID (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
                                          (paired_cons pairing _ _ (paired_optional pairing [51, 55, 56] record.execRestatementReason (by decide) (by decide))
                                           (paired_cons pairing _ _ (paired_optional pairing [52, 51, 50] record.expireDate (by decide) (by decide))
                                            (paired_cons pairing _ _ (paired_optional pairing [53, 50, 55] record.secondaryExecID (by decide) (by decide))
                                             (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                                              (paired_cons pairing _ _ (paired_optional pairing [54, 50, 53] record.tradingSessionSubID (by decide) (by decide))
                                               (paired_cons pairing _ _ (paired_optional pairing [56, 53, 49] record.lastLiquidityInd (by decide) (by decide))
                                                (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                                                 (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 48] record.refOrderID (by decide) (by decide))
                                                  (paired_cons pairing _ _ (paired_optional pairing [49, 48, 56, 49] record.refOrderIDSource (by decide) (by decide))
                                                   (paired_cons pairing _ _ (paired_optional pairing [49, 56, 49, 53] record.tradingCapacity (by decide) (by decide))
                                                    (paired_cons pairing _ _ (paired_optional pairing [50, 53, 50, 51] record.crossedIndicator (by decide) (by decide))
                                                     (paired_cons pairing _ _ (paired_optional pairing [49, 56, 50, 51] record.triggered (by decide) (by decide))
                                                      (paired_cons pairing _ _ (paired_optional pairing [50, 53, 50, 52, 53] record.bBOSetting (by decide) (by decide))
                                                       (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 48, 56] record.freeText2 (by decide) (by decide))
                                                        (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 48, 55] record.freeText4 (by decide) (by decide))
                                                         (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
                                                          (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 48, 56] record.orderIDSfx (by decide) (by decide))
                                                           (paired_cons pairing _ _ (paired_optional pairing [51, 48, 54, 50, 53] record.tradeAtCloseOptIn (by decide) (by decide))
                                                            (paired_none pairing))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  password : Option (Terminated 1)  -- tag 554
  resetSeqNumFlag : Option (Terminated 1)  -- tag 141
  fIXEngineName : Option (Terminated 1)  -- tag 1600
  fIXEngineVersion : Option (Terminated 1)  -- tag 1601
  fIXEngineVendor : Option (Terminated 1)  -- tag 1602
  applicationSystemName : Option (Terminated 1)  -- tag 1603
  applicationSystemVersion : Option (Terminated 1)  -- tag 1604
  applicationSystemVendor : Option (Terminated 1)  -- tag 1605
  defaultCstmApplVerID : Terminated 1  -- tag 1408
  defaultCstmApplVerSubID : Option (Terminated 1)  -- tag 28763
  tradSesMode : Option (Terminated 1)  -- tag 339
  throttleInst : Terminated 1  -- tag 1685
  throttleMaxQueueTime : Option (Terminated 1)  -- tag 28790

def Logon.parts (record : Logon) : List Part :=
  [Part.required [57, 56] record.encryptMethod,
   Part.required [49, 48, 56] record.heartBtInt,
   Part.optional [53, 53, 52] record.password,
   Part.optional [49, 52, 49] record.resetSeqNumFlag,
   Part.optional [49, 54, 48, 48] record.fIXEngineName,
   Part.optional [49, 54, 48, 49] record.fIXEngineVersion,
   Part.optional [49, 54, 48, 50] record.fIXEngineVendor,
   Part.optional [49, 54, 48, 51] record.applicationSystemName,
   Part.optional [49, 54, 48, 52] record.applicationSystemVersion,
   Part.optional [49, 54, 48, 53] record.applicationSystemVendor,
   Part.required [49, 52, 48, 56] record.defaultCstmApplVerID,
   Part.optional [50, 56, 55, 54, 51] record.defaultCstmApplVerSubID,
   Part.optional [51, 51, 57] record.tradSesMode,
   Part.required [49, 54, 56, 53] record.throttleInst,
   Part.optional [50, 56, 55, 57, 48] record.throttleMaxQueueTime]

def Logon.tags : List (List (List UInt8)) :=
  [[[57, 56]], [[49, 48, 56]], [[53, 53, 52]], [[49, 52, 49]], [[49, 54, 48, 48]], [[49, 54, 48, 49]], [[49, 54, 48, 50]], [[49, 54, 48, 51]], [[49, 54, 48, 52]], [[49, 54, 48, 53]], [[49, 52, 48, 56]], [[50, 56, 55, 54, 51]], [[51, 51, 57]], [[49, 54, 56, 53]], [[50, 56, 55, 57, 48]]]

theorem Logon.shape (record : Logon) : record.parts.map Part.tags = Logon.tags := rfl

def Logon.decode (tokens : List Token) : Option Logon := do
  let encryptMethod ← readRequired [57, 56] tokens
  let heartBtInt ← readRequired [49, 48, 56] tokens
  let password ← readOptional [53, 53, 52] tokens
  let resetSeqNumFlag ← readOptional [49, 52, 49] tokens
  let fIXEngineName ← readOptional [49, 54, 48, 48] tokens
  let fIXEngineVersion ← readOptional [49, 54, 48, 49] tokens
  let fIXEngineVendor ← readOptional [49, 54, 48, 50] tokens
  let applicationSystemName ← readOptional [49, 54, 48, 51] tokens
  let applicationSystemVersion ← readOptional [49, 54, 48, 52] tokens
  let applicationSystemVendor ← readOptional [49, 54, 48, 53] tokens
  let defaultCstmApplVerID ← readRequired [49, 52, 48, 56] tokens
  let defaultCstmApplVerSubID ← readOptional [50, 56, 55, 54, 51] tokens
  let tradSesMode ← readOptional [51, 51, 57] tokens
  let throttleInst ← readRequired [49, 54, 56, 53] tokens
  let throttleMaxQueueTime ← readOptional [50, 56, 55, 57, 48] tokens
  pure { encryptMethod, heartBtInt, password, resetSeqNumFlag, fIXEngineName, fIXEngineVersion, fIXEngineVendor, applicationSystemName, applicationSystemVersion, applicationSystemVendor, defaultCstmApplVerID, defaultCstmApplVerSubID, tradSesMode, throttleInst, throttleMaxQueueTime }

theorem Logon.decode_agrees (record : Logon) (tokens : List Token)
    (agrees : ∀ tags ∈ Logon.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logon.decode tokens = some record := by
  have distinct : Logon.tags.flatten.Nodup := by decide +kernel
  have encryptMethod := readRequired_part [57, 56] record.encryptMethod tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have heartBtInt := readRequired_part [49, 48, 56] record.heartBtInt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have password := readOptional_part [53, 53, 52] record.password tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have resetSeqNumFlag := readOptional_part [49, 52, 49] record.resetSeqNumFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have fIXEngineName := readOptional_part [49, 54, 48, 48] record.fIXEngineName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have fIXEngineVersion := readOptional_part [49, 54, 48, 49] record.fIXEngineVersion tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have fIXEngineVendor := readOptional_part [49, 54, 48, 50] record.fIXEngineVendor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have applicationSystemName := readOptional_part [49, 54, 48, 51] record.applicationSystemName tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have applicationSystemVersion := readOptional_part [49, 54, 48, 52] record.applicationSystemVersion tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have applicationSystemVendor := readOptional_part [49, 54, 48, 53] record.applicationSystemVendor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have defaultCstmApplVerID := readRequired_part [49, 52, 48, 56] record.defaultCstmApplVerID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have defaultCstmApplVerSubID := readOptional_part [50, 56, 55, 54, 51] record.defaultCstmApplVerSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tradSesMode := readOptional_part [51, 51, 57] record.tradSesMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have throttleInst := readRequired_part [49, 54, 56, 53] record.throttleInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have throttleMaxQueueTime := readOptional_part [50, 56, 55, 57, 48] record.throttleMaxQueueTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [Logon.decode, encryptMethod, heartBtInt, password, resetSeqNumFlag, fIXEngineName, fIXEngineVersion, fIXEngineVendor, applicationSystemName, applicationSystemVersion, applicationSystemVendor, defaultCstmApplVerID, defaultCstmApplVerSubID, tradSesMode, throttleInst, throttleMaxQueueTime, some_bind] <;> rfl

theorem Logon.taken (record : Logon) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 56] record.encryptMethod (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 48, 56] record.heartBtInt (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [53, 53, 52] record.password (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 52, 49] record.resetSeqNumFlag (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 48] record.fIXEngineName (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 49] record.fIXEngineVersion (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 50] record.fIXEngineVendor (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 51] record.applicationSystemName (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 52] record.applicationSystemVersion (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 54, 48, 53] record.applicationSystemVendor (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [49, 52, 48, 56] record.defaultCstmApplVerID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 54, 51] record.defaultCstmApplVerSubID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [51, 51, 57] record.tradSesMode (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [49, 54, 56, 53] record.throttleInst (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 57, 48] record.throttleMaxQueueTime (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

structure Logout where
  text : Option (Terminated 1)  -- tag 58
  sessionStatus : Option (Terminated 1)  -- tag 1409

def Logout.parts (record : Logout) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.optional [49, 52, 48, 57] record.sessionStatus]

def Logout.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[49, 52, 48, 57]]]

theorem Logout.shape (record : Logout) : record.parts.map Part.tags = Logout.tags := rfl

def Logout.decode (tokens : List Token) : Option Logout := do
  let text ← readOptional [53, 56] tokens
  let sessionStatus ← readOptional [49, 52, 48, 57] tokens
  pure { text, sessionStatus }

theorem Logout.decode_agrees (record : Logout) (tokens : List Token)
    (agrees : ∀ tags ∈ Logout.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Logout.decode tokens = some record := by
  have distinct : Logout.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sessionStatus := readOptional_part [49, 52, 48, 57] record.sessionStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [Logout.decode, text, sessionStatus, some_bind] <;> rfl

theorem Logout.taken (record : Logout) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 52, 48, 57] record.sessionStatus (by decide) (by decide))
    (paired_none pairing))

structure Quote where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  currency : Option (Terminated 1)  -- tag 15
  quoteID : Terminated 1  -- tag 117
  quoteReqID : Terminated 1  -- tag 131
  bidPx : Option (Terminated 1)  -- tag 132
  offerPx : Option (Terminated 1)  -- tag 133
  bidSize : Option (Terminated 1)  -- tag 134
  offerSize : Option (Terminated 1)  -- tag 135

def Quote.parts (record : Quote) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.optional [49, 53] record.currency,
   Part.required [49, 49, 55] record.quoteID,
   Part.required [49, 51, 49] record.quoteReqID,
   Part.optional [49, 51, 50] record.bidPx,
   Part.optional [49, 51, 51] record.offerPx,
   Part.optional [49, 51, 52] record.bidSize,
   Part.optional [49, 51, 53] record.offerSize]

def Quote.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [[49, 53]], [[49, 49, 55]], [[49, 51, 49]], [[49, 51, 50]], [[49, 51, 51]], [[49, 51, 52]], [[49, 51, 53]]]

theorem Quote.shape (record : Quote) : record.parts.map Part.tags = Quote.tags := rfl

def Quote.decode (tokens : List Token) : Option Quote := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let currency ← readOptional [49, 53] tokens
  let quoteID ← readRequired [49, 49, 55] tokens
  let quoteReqID ← readRequired [49, 51, 49] tokens
  let bidPx ← readOptional [49, 51, 50] tokens
  let offerPx ← readOptional [49, 51, 51] tokens
  let bidSize ← readOptional [49, 51, 52] tokens
  let offerSize ← readOptional [49, 51, 53] tokens
  pure { symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, quoteID, quoteReqID, bidPx, offerPx, bidSize, offerSize }

theorem Quote.decode_agrees (record : Quote) (tokens : List Token)
    (agrees : ∀ tags ∈ Quote.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Quote.decode tokens = some record := by
  have distinct : Quote.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have currency := readOptional_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have quoteID := readRequired_part [49, 49, 55] record.quoteID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have quoteReqID := readRequired_part [49, 51, 49] record.quoteReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have bidPx := readOptional_part [49, 51, 50] record.bidPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have offerPx := readOptional_part [49, 51, 51] record.offerPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have bidSize := readOptional_part [49, 51, 52] record.bidSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have offerSize := readOptional_part [49, 51, 53] record.offerSize tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  simp only [Quote.decode, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, currency, quoteID, quoteReqID, bidPx, offerPx, bidSize, offerSize, some_bind] <;> rfl

theorem Quote.taken (record : Quote) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within (by decide) (by decide) NoSecurityAltID.taken record.noSecurityAltID)
      (paired_cons pairing _ _ (paired_optional pairing [50, 50, 51] record.couponRate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 48] record.deliveryType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 53] record.currency (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [49, 49, 55] record.quoteID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [49, 51, 49] record.quoteReqID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50] record.bidPx (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 51, 51] record.offerPx (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 51, 52] record.bidSize (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 51, 53] record.offerSize (by decide) (by decide))
                 (paired_none pairing)))))))))))))))

structure Reject where
  refSeqNum : Terminated 1  -- tag 45
  text : Option (Terminated 1)  -- tag 58
  refTagID : Option (Terminated 1)  -- tag 371
  refMsgType : Terminated 1  -- tag 372
  sessionRejectReason : Option (Terminated 1)  -- tag 373
  returnCode : Option (Terminated 1)  -- tag 25023

def Reject.parts (record : Reject) : List Part :=
  [Part.required [52, 53] record.refSeqNum,
   Part.optional [53, 56] record.text,
   Part.optional [51, 55, 49] record.refTagID,
   Part.required [51, 55, 50] record.refMsgType,
   Part.optional [51, 55, 51] record.sessionRejectReason,
   Part.optional [50, 53, 48, 50, 51] record.returnCode]

def Reject.tags : List (List (List UInt8)) :=
  [[[52, 53]], [[53, 56]], [[51, 55, 49]], [[51, 55, 50]], [[51, 55, 51]], [[50, 53, 48, 50, 51]]]

theorem Reject.shape (record : Reject) : record.parts.map Part.tags = Reject.tags := rfl

def Reject.decode (tokens : List Token) : Option Reject := do
  let refSeqNum ← readRequired [52, 53] tokens
  let text ← readOptional [53, 56] tokens
  let refTagID ← readOptional [51, 55, 49] tokens
  let refMsgType ← readRequired [51, 55, 50] tokens
  let sessionRejectReason ← readOptional [51, 55, 51] tokens
  let returnCode ← readOptional [50, 53, 48, 50, 51] tokens
  pure { refSeqNum, text, refTagID, refMsgType, sessionRejectReason, returnCode }

theorem Reject.decode_agrees (record : Reject) (tokens : List Token)
    (agrees : ∀ tags ∈ Reject.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Reject.decode tokens = some record := by
  have distinct : Reject.tags.flatten.Nodup := by decide +kernel
  have refSeqNum := readRequired_part [52, 53] record.refSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have refTagID := readOptional_part [51, 55, 49] record.refTagID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have refMsgType := readRequired_part [51, 55, 50] record.refMsgType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sessionRejectReason := readOptional_part [51, 55, 51] record.sessionRejectReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have returnCode := readOptional_part [50, 53, 48, 50, 51] record.returnCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [Reject.decode, refSeqNum, text, refTagID, refMsgType, sessionRejectReason, returnCode, some_bind] <;> rfl

theorem Reject.taken (record : Reject) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 53] record.refSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [51, 55, 49] record.refTagID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 55, 50] record.refMsgType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [51, 55, 51] record.sessionRejectReason (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 50, 51] record.returnCode (by decide) (by decide))
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

structure SecurityStatus where
  securityReqID : Terminated 1  -- tag 320
  securityStatusReportID : Option (Terminated 1)  -- tag 28781

def SecurityStatus.parts (record : SecurityStatus) : List Part :=
  [Part.required [51, 50, 48] record.securityReqID,
   Part.optional [50, 56, 55, 56, 49] record.securityStatusReportID]

def SecurityStatus.tags : List (List (List UInt8)) :=
  [[[51, 50, 48]], [[50, 56, 55, 56, 49]]]

theorem SecurityStatus.shape (record : SecurityStatus) : record.parts.map Part.tags = SecurityStatus.tags := rfl

def SecurityStatus.decode (tokens : List Token) : Option SecurityStatus := do
  let securityReqID ← readRequired [51, 50, 48] tokens
  let securityStatusReportID ← readOptional [50, 56, 55, 56, 49] tokens
  pure { securityReqID, securityStatusReportID }

theorem SecurityStatus.decode_agrees (record : SecurityStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ SecurityStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SecurityStatus.decode tokens = some record := by
  have distinct : SecurityStatus.tags.flatten.Nodup := by decide +kernel
  have securityReqID := readRequired_part [51, 50, 48] record.securityReqID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityStatusReportID := readOptional_part [50, 56, 55, 56, 49] record.securityStatusReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SecurityStatus.decode, securityReqID, securityStatusReportID, some_bind] <;> rfl

theorem SecurityStatus.taken (record : SecurityStatus) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 50, 48] record.securityReqID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 56, 49] record.securityStatusReportID (by decide) (by decide))
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

structure NoSessions where
  gatewaySessionID : Terminated 1  -- tag 28766
  sessionMode : Terminated 1  -- tag 28730
  sessionSubMode : Terminated 1  -- tag 28735
  secondarySessionID : Option (Terminated 1)  -- tag 28767

def NoSessions.parts (record : NoSessions) : List Part :=
  [Part.required [50, 56, 55, 54, 54] record.gatewaySessionID,
   Part.required [50, 56, 55, 51, 48] record.sessionMode,
   Part.required [50, 56, 55, 51, 53] record.sessionSubMode,
   Part.optional [50, 56, 55, 54, 55] record.secondarySessionID]

def NoSessions.tags : List (List (List UInt8)) :=
  [[[50, 56, 55, 54, 54]], [[50, 56, 55, 51, 48]], [[50, 56, 55, 51, 53]], [[50, 56, 55, 54, 55]]]

theorem NoSessions.shape (record : NoSessions) : record.parts.map Part.tags = NoSessions.tags := rfl

def NoSessions.decode (tokens : List Token) : Option NoSessions := do
  let gatewaySessionID ← readRequired [50, 56, 55, 54, 54] tokens
  let sessionMode ← readRequired [50, 56, 55, 51, 48] tokens
  let sessionSubMode ← readRequired [50, 56, 55, 51, 53] tokens
  let secondarySessionID ← readOptional [50, 56, 55, 54, 55] tokens
  pure { gatewaySessionID, sessionMode, sessionSubMode, secondarySessionID }

theorem NoSessions.decode_agrees (record : NoSessions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSessions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSessions.decode tokens = some record := by
  have distinct : NoSessions.tags.flatten.Nodup := by decide +kernel
  have gatewaySessionID := readRequired_part [50, 56, 55, 54, 54] record.gatewaySessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sessionMode := readRequired_part [50, 56, 55, 51, 48] record.sessionMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sessionSubMode := readRequired_part [50, 56, 55, 51, 53] record.sessionSubMode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have secondarySessionID := readOptional_part [50, 56, 55, 54, 55] record.secondarySessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoSessions.decode, gatewaySessionID, sessionMode, sessionSubMode, secondarySessionID, some_bind] <;> rfl

theorem NoSessions.taken (record : NoSessions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 54, 54] record.gatewaySessionID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 51, 48] record.sessionMode (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 51, 53] record.sessionSubMode (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 54, 55] record.secondarySessionID (by decide) (by decide))
      (paired_none pairing))))

def NoSessions.members : List (List UInt8) := NoSessions.tags.flatten

def NoSessions.encode (entry : NoSessions) : List Token := encodeParts entry.parts

theorem NoSessions.decode_encode (entry : NoSessions) : NoSessions.decode entry.encode = some entry :=
  NoSessions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSessions.within (entry : NoSessions) : ∀ token ∈ entry.encode, token.tag ∈ NoSessions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSessions.shape] at this

theorem NoSessions.led (entry : NoSessions) : Lead [50, 56, 55, 54, 54] entry.encode :=
  lead_parts [50, 56, 55, 54, 54] entry.gatewaySessionID _ NoSessions.tags.tail rfl (by decide +kernel)

structure SessionDetailsList where
  noSessions : List NoSessions  -- tag 28734
  uTransactTime : Terminated 1  -- tag 30060

def SessionDetailsList.parts (record : SessionDetailsList) : List Part :=
  [Part.group [50, 56, 55, 51, 52] NoSessions.members NoSessions.encode NoSessions.within record.noSessions,
   Part.required [51, 48, 48, 54, 48] record.uTransactTime]

def SessionDetailsList.tags : List (List (List UInt8)) :=
  [[50, 56, 55, 51, 52] :: NoSessions.members, [[51, 48, 48, 54, 48]]]

theorem SessionDetailsList.shape (record : SessionDetailsList) : record.parts.map Part.tags = SessionDetailsList.tags := rfl

def SessionDetailsList.decode (tokens : List Token) : Option SessionDetailsList := do
  let noSessions ← readGroup [50, 56, 55, 51, 52] [50, 56, 55, 54, 54] NoSessions.members NoSessions.decode tokens
  let uTransactTime ← readRequired [51, 48, 48, 54, 48] tokens
  pure { noSessions, uTransactTime }

theorem SessionDetailsList.decode_agrees (record : SessionDetailsList) (tokens : List Token)
    (agrees : ∀ tags ∈ SessionDetailsList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    SessionDetailsList.decode tokens = some record := by
  have distinct : SessionDetailsList.tags.flatten.Nodup := by decide +kernel
  have noSessions := readGroup_part [50, 56, 55, 51, 52] [50, 56, 55, 54, 54] NoSessions.members NoSessions.encode NoSessions.within NoSessions.decode NoSessions.decode_encode NoSessions.led record.noSessions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have uTransactTime := readRequired_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [SessionDetailsList.decode, noSessions, uTransactTime, some_bind] <;> rfl

theorem SessionDetailsList.taken (record : SessionDetailsList) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [50, 56, 55, 51, 52] NoSessions.members NoSessions.encode NoSessions.within (by decide) (by decide) NoSessions.taken record.noSessions)
   (paired_cons pairing _ _ (paired_required pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
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

structure NoRegulatoryTradeIDs where
  regulatoryTradeID : Terminated 1  -- tag 1903
  regulatoryTradeIDType : Option (Terminated 1)  -- tag 1906

def NoRegulatoryTradeIDs.parts (record : NoRegulatoryTradeIDs) : List Part :=
  [Part.required [49, 57, 48, 51] record.regulatoryTradeID,
   Part.optional [49, 57, 48, 54] record.regulatoryTradeIDType]

def NoRegulatoryTradeIDs.tags : List (List (List UInt8)) :=
  [[[49, 57, 48, 51]], [[49, 57, 48, 54]]]

theorem NoRegulatoryTradeIDs.shape (record : NoRegulatoryTradeIDs) : record.parts.map Part.tags = NoRegulatoryTradeIDs.tags := rfl

def NoRegulatoryTradeIDs.decode (tokens : List Token) : Option NoRegulatoryTradeIDs := do
  let regulatoryTradeID ← readRequired [49, 57, 48, 51] tokens
  let regulatoryTradeIDType ← readOptional [49, 57, 48, 54] tokens
  pure { regulatoryTradeID, regulatoryTradeIDType }

theorem NoRegulatoryTradeIDs.decode_agrees (record : NoRegulatoryTradeIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRegulatoryTradeIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRegulatoryTradeIDs.decode tokens = some record := by
  have distinct : NoRegulatoryTradeIDs.tags.flatten.Nodup := by decide +kernel
  have regulatoryTradeID := readRequired_part [49, 57, 48, 51] record.regulatoryTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have regulatoryTradeIDType := readOptional_part [49, 57, 48, 54] record.regulatoryTradeIDType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoRegulatoryTradeIDs.decode, regulatoryTradeID, regulatoryTradeIDType, some_bind] <;> rfl

theorem NoRegulatoryTradeIDs.taken (record : NoRegulatoryTradeIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 57, 48, 51] record.regulatoryTradeID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 57, 48, 54] record.regulatoryTradeIDType (by decide) (by decide))
    (paired_none pairing))

def NoRegulatoryTradeIDs.members : List (List UInt8) := NoRegulatoryTradeIDs.tags.flatten

def NoRegulatoryTradeIDs.encode (entry : NoRegulatoryTradeIDs) : List Token := encodeParts entry.parts

theorem NoRegulatoryTradeIDs.decode_encode (entry : NoRegulatoryTradeIDs) : NoRegulatoryTradeIDs.decode entry.encode = some entry :=
  NoRegulatoryTradeIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRegulatoryTradeIDs.within (entry : NoRegulatoryTradeIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRegulatoryTradeIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRegulatoryTradeIDs.shape] at this

theorem NoRegulatoryTradeIDs.led (entry : NoRegulatoryTradeIDs) : Lead [49, 57, 48, 51] entry.encode :=
  lead_parts [49, 57, 48, 51] entry.regulatoryTradeID _ NoRegulatoryTradeIDs.tags.tail rfl (by decide +kernel)

structure NoSRQSRelatedTradeIDs where
  sRQSRelatedTradeID : Terminated 1  -- tag 25152

def NoSRQSRelatedTradeIDs.parts (record : NoSRQSRelatedTradeIDs) : List Part :=
  [Part.required [50, 53, 49, 53, 50] record.sRQSRelatedTradeID]

def NoSRQSRelatedTradeIDs.tags : List (List (List UInt8)) :=
  [[[50, 53, 49, 53, 50]]]

theorem NoSRQSRelatedTradeIDs.shape (record : NoSRQSRelatedTradeIDs) : record.parts.map Part.tags = NoSRQSRelatedTradeIDs.tags := rfl

def NoSRQSRelatedTradeIDs.decode (tokens : List Token) : Option NoSRQSRelatedTradeIDs := do
  let sRQSRelatedTradeID ← readRequired [50, 53, 49, 53, 50] tokens
  pure { sRQSRelatedTradeID }

theorem NoSRQSRelatedTradeIDs.decode_agrees (record : NoSRQSRelatedTradeIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSRQSRelatedTradeIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSRQSRelatedTradeIDs.decode tokens = some record := by
  have distinct : NoSRQSRelatedTradeIDs.tags.flatten.Nodup := by decide +kernel
  have sRQSRelatedTradeID := readRequired_part [50, 53, 49, 53, 50] record.sRQSRelatedTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoSRQSRelatedTradeIDs.decode, sRQSRelatedTradeID, some_bind] <;> rfl

theorem NoSRQSRelatedTradeIDs.taken (record : NoSRQSRelatedTradeIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 53, 49, 53, 50] record.sRQSRelatedTradeID (by decide) (by decide))
   (paired_none pairing)

def NoSRQSRelatedTradeIDs.members : List (List UInt8) := NoSRQSRelatedTradeIDs.tags.flatten

def NoSRQSRelatedTradeIDs.encode (entry : NoSRQSRelatedTradeIDs) : List Token := encodeParts entry.parts

theorem NoSRQSRelatedTradeIDs.decode_encode (entry : NoSRQSRelatedTradeIDs) : NoSRQSRelatedTradeIDs.decode entry.encode = some entry :=
  NoSRQSRelatedTradeIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoSRQSRelatedTradeIDs.within (entry : NoSRQSRelatedTradeIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoSRQSRelatedTradeIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoSRQSRelatedTradeIDs.shape] at this

theorem NoSRQSRelatedTradeIDs.led (entry : NoSRQSRelatedTradeIDs) : Lead [50, 53, 49, 53, 50] entry.encode :=
  lead_parts [50, 53, 49, 53, 50] entry.sRQSRelatedTradeID _ NoSRQSRelatedTradeIDs.tags.tail rfl (by decide +kernel)

structure NoRootPartyIDs where
  rootPartyID : Terminated 1  -- tag 1117
  rootPartyIDSource : Terminated 1  -- tag 1118
  rootPartyRole : Terminated 1  -- tag 1119

def NoRootPartyIDs.parts (record : NoRootPartyIDs) : List Part :=
  [Part.required [49, 49, 49, 55] record.rootPartyID,
   Part.required [49, 49, 49, 56] record.rootPartyIDSource,
   Part.required [49, 49, 49, 57] record.rootPartyRole]

def NoRootPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 49, 49, 55]], [[49, 49, 49, 56]], [[49, 49, 49, 57]]]

theorem NoRootPartyIDs.shape (record : NoRootPartyIDs) : record.parts.map Part.tags = NoRootPartyIDs.tags := rfl

def NoRootPartyIDs.decode (tokens : List Token) : Option NoRootPartyIDs := do
  let rootPartyID ← readRequired [49, 49, 49, 55] tokens
  let rootPartyIDSource ← readRequired [49, 49, 49, 56] tokens
  let rootPartyRole ← readRequired [49, 49, 49, 57] tokens
  pure { rootPartyID, rootPartyIDSource, rootPartyRole }

theorem NoRootPartyIDs.decode_agrees (record : NoRootPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRootPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRootPartyIDs.decode tokens = some record := by
  have distinct : NoRootPartyIDs.tags.flatten.Nodup := by decide +kernel
  have rootPartyID := readRequired_part [49, 49, 49, 55] record.rootPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have rootPartyIDSource := readRequired_part [49, 49, 49, 56] record.rootPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have rootPartyRole := readRequired_part [49, 49, 49, 57] record.rootPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRootPartyIDs.decode, rootPartyID, rootPartyIDSource, rootPartyRole, some_bind] <;> rfl

theorem NoRootPartyIDs.taken (record : NoRootPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49, 49, 55] record.rootPartyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49, 49, 56] record.rootPartyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 49, 49, 57] record.rootPartyRole (by decide) (by decide))
     (paired_none pairing)))

def NoRootPartyIDs.members : List (List UInt8) := NoRootPartyIDs.tags.flatten

def NoRootPartyIDs.encode (entry : NoRootPartyIDs) : List Token := encodeParts entry.parts

theorem NoRootPartyIDs.decode_encode (entry : NoRootPartyIDs) : NoRootPartyIDs.decode entry.encode = some entry :=
  NoRootPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRootPartyIDs.within (entry : NoRootPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRootPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRootPartyIDs.shape] at this

theorem NoRootPartyIDs.led (entry : NoRootPartyIDs) : Lead [49, 49, 49, 55] entry.encode :=
  lead_parts [49, 49, 49, 55] entry.rootPartyID _ NoRootPartyIDs.tags.tail rfl (by decide +kernel)

structure NoClearingInstructions where
  clearingInstruction : Terminated 1  -- tag 577

def NoClearingInstructions.parts (record : NoClearingInstructions) : List Part :=
  [Part.required [53, 55, 55] record.clearingInstruction]

def NoClearingInstructions.tags : List (List (List UInt8)) :=
  [[[53, 55, 55]]]

theorem NoClearingInstructions.shape (record : NoClearingInstructions) : record.parts.map Part.tags = NoClearingInstructions.tags := rfl

def NoClearingInstructions.decode (tokens : List Token) : Option NoClearingInstructions := do
  let clearingInstruction ← readRequired [53, 55, 55] tokens
  pure { clearingInstruction }

theorem NoClearingInstructions.decode_agrees (record : NoClearingInstructions) (tokens : List Token)
    (agrees : ∀ tags ∈ NoClearingInstructions.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoClearingInstructions.decode tokens = some record := by
  have distinct : NoClearingInstructions.tags.flatten.Nodup := by decide +kernel
  have clearingInstruction := readRequired_part [53, 55, 55] record.clearingInstruction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoClearingInstructions.decode, clearingInstruction, some_bind] <;> rfl

theorem NoClearingInstructions.taken (record : NoClearingInstructions) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 55, 55] record.clearingInstruction (by decide) (by decide))
   (paired_none pairing)

def NoClearingInstructions.members : List (List UInt8) := NoClearingInstructions.tags.flatten

def NoClearingInstructions.encode (entry : NoClearingInstructions) : List Token := encodeParts entry.parts

theorem NoClearingInstructions.decode_encode (entry : NoClearingInstructions) : NoClearingInstructions.decode entry.encode = some entry :=
  NoClearingInstructions.decode_agrees entry _ (fun _ _ => rfl)

theorem NoClearingInstructions.within (entry : NoClearingInstructions) : ∀ token ∈ entry.encode, token.tag ∈ NoClearingInstructions.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoClearingInstructions.shape] at this

theorem NoClearingInstructions.led (entry : NoClearingInstructions) : Lead [53, 55, 55] entry.encode :=
  lead_parts [53, 55, 55] entry.clearingInstruction _ NoClearingInstructions.tags.tail rfl (by decide +kernel)

structure NoOrderAttributes where
  orderAttributeType : Terminated 1  -- tag 2594
  orderAttributeValue : Option (Terminated 1)  -- tag 2595

def NoOrderAttributes.parts (record : NoOrderAttributes) : List Part :=
  [Part.required [50, 53, 57, 52] record.orderAttributeType,
   Part.optional [50, 53, 57, 53] record.orderAttributeValue]

def NoOrderAttributes.tags : List (List (List UInt8)) :=
  [[[50, 53, 57, 52]], [[50, 53, 57, 53]]]

theorem NoOrderAttributes.shape (record : NoOrderAttributes) : record.parts.map Part.tags = NoOrderAttributes.tags := rfl

def NoOrderAttributes.decode (tokens : List Token) : Option NoOrderAttributes := do
  let orderAttributeType ← readRequired [50, 53, 57, 52] tokens
  let orderAttributeValue ← readOptional [50, 53, 57, 53] tokens
  pure { orderAttributeType, orderAttributeValue }

theorem NoOrderAttributes.decode_agrees (record : NoOrderAttributes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrderAttributes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrderAttributes.decode tokens = some record := by
  have distinct : NoOrderAttributes.tags.flatten.Nodup := by decide +kernel
  have orderAttributeType := readRequired_part [50, 53, 57, 52] record.orderAttributeType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderAttributeValue := readOptional_part [50, 53, 57, 53] record.orderAttributeValue tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoOrderAttributes.decode, orderAttributeType, orderAttributeValue, some_bind] <;> rfl

theorem NoOrderAttributes.taken (record : NoOrderAttributes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [50, 53, 57, 52] record.orderAttributeType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 53, 57, 53] record.orderAttributeValue (by decide) (by decide))
    (paired_none pairing))

def NoOrderAttributes.members : List (List UInt8) := NoOrderAttributes.tags.flatten

def NoOrderAttributes.encode (entry : NoOrderAttributes) : List Token := encodeParts entry.parts

theorem NoOrderAttributes.decode_encode (entry : NoOrderAttributes) : NoOrderAttributes.decode entry.encode = some entry :=
  NoOrderAttributes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrderAttributes.within (entry : NoOrderAttributes) : ∀ token ∈ entry.encode, token.tag ∈ NoOrderAttributes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrderAttributes.shape] at this

theorem NoOrderAttributes.led (entry : NoOrderAttributes) : Lead [50, 53, 57, 52] entry.encode :=
  lead_parts [50, 53, 57, 52] entry.orderAttributeType _ NoOrderAttributes.tags.tail rfl (by decide +kernel)

structure NoSides where
  side : Terminated 1  -- tag 54
  sideTradeReportID : Option (Terminated 1)  -- tag 1005
  sideTradeID : Option (Terminated 1)  -- tag 1506
  noPartyIDs : List NoPartyIDs  -- tag 453
  partyIDClearingUnit : Option (Terminated 1)  -- tag 25027
  partyIDSettlementUnit : Option (Terminated 1)  -- tag 25120
  account : Option (Terminated 1)  -- tag 1
  noClearingInstructions : List NoClearingInstructions  -- tag 576
  numDaysInterest : Option (Terminated 1)  -- tag 157
  accruedInterestAmt : Option (Terminated 1)  -- tag 159
  settlCurrAmt : Option (Terminated 1)  -- tag 119
  settlCurrFxRate : Option (Terminated 1)  -- tag 155
  freeText1 : Option (Terminated 1)  -- tag 25007
  sideGrossTradeAmt : Option (Terminated 1)  -- tag 1072
  orderCategory : Option (Terminated 1)  -- tag 1115
  sideLiquidityInd : Option (Terminated 1)  -- tag 1444
  orderID : Option (Terminated 1)  -- tag 37
  clOrdID : Option (Terminated 1)  -- tag 11
  ordType : Option (Terminated 1)  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  leavesQty : Option (Terminated 1)  -- tag 151
  cumQty : Option (Terminated 1)  -- tag 14
  noOrderAttributes : List NoOrderAttributes  -- tag 2593
  freeText2 : Option (Terminated 1)  -- tag 25008
  freeText4 : Option (Terminated 1)  -- tag 25107
  orderIDSfx : Option (Terminated 1)  -- tag 25108

def NoSides.parts (record : NoSides) : List Part :=
  [Part.required [53, 52] record.side,
   Part.optional [49, 48, 48, 53] record.sideTradeReportID,
   Part.optional [49, 53, 48, 54] record.sideTradeID,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [50, 53, 48, 50, 55] record.partyIDClearingUnit,
   Part.optional [50, 53, 49, 50, 48] record.partyIDSettlementUnit,
   Part.optional [49] record.account,
   Part.group [53, 55, 54] NoClearingInstructions.members NoClearingInstructions.encode NoClearingInstructions.within record.noClearingInstructions,
   Part.optional [49, 53, 55] record.numDaysInterest,
   Part.optional [49, 53, 57] record.accruedInterestAmt,
   Part.optional [49, 49, 57] record.settlCurrAmt,
   Part.optional [49, 53, 53] record.settlCurrFxRate,
   Part.optional [50, 53, 48, 48, 55] record.freeText1,
   Part.optional [49, 48, 55, 50] record.sideGrossTradeAmt,
   Part.optional [49, 49, 49, 53] record.orderCategory,
   Part.optional [49, 52, 52, 52] record.sideLiquidityInd,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 53, 49] record.leavesQty,
   Part.optional [49, 52] record.cumQty,
   Part.group [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within record.noOrderAttributes,
   Part.optional [50, 53, 48, 48, 56] record.freeText2,
   Part.optional [50, 53, 49, 48, 55] record.freeText4,
   Part.optional [50, 53, 49, 48, 56] record.orderIDSfx]

def NoSides.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[49, 48, 48, 53]], [[49, 53, 48, 54]], [52, 53, 51] :: NoPartyIDs.members, [[50, 53, 48, 50, 55]], [[50, 53, 49, 50, 48]], [[49]], [53, 55, 54] :: NoClearingInstructions.members, [[49, 53, 55]], [[49, 53, 57]], [[49, 49, 57]], [[49, 53, 53]], [[50, 53, 48, 48, 55]], [[49, 48, 55, 50]], [[49, 49, 49, 53]], [[49, 52, 52, 52]], [[51, 55]], [[49, 49]], [[52, 48]], [[52, 52]], [[49, 53, 49]], [[49, 52]], [50, 53, 57, 51] :: NoOrderAttributes.members, [[50, 53, 48, 48, 56]], [[50, 53, 49, 48, 55]], [[50, 53, 49, 48, 56]]]

theorem NoSides.shape (record : NoSides) : record.parts.map Part.tags = NoSides.tags := rfl

def NoSides.decode (tokens : List Token) : Option NoSides := do
  let side ← readRequired [53, 52] tokens
  let sideTradeReportID ← readOptional [49, 48, 48, 53] tokens
  let sideTradeID ← readOptional [49, 53, 48, 54] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let partyIDClearingUnit ← readOptional [50, 53, 48, 50, 55] tokens
  let partyIDSettlementUnit ← readOptional [50, 53, 49, 50, 48] tokens
  let account ← readOptional [49] tokens
  let noClearingInstructions ← readGroup [53, 55, 54] [53, 55, 55] NoClearingInstructions.members NoClearingInstructions.decode tokens
  let numDaysInterest ← readOptional [49, 53, 55] tokens
  let accruedInterestAmt ← readOptional [49, 53, 57] tokens
  let settlCurrAmt ← readOptional [49, 49, 57] tokens
  let settlCurrFxRate ← readOptional [49, 53, 53] tokens
  let freeText1 ← readOptional [50, 53, 48, 48, 55] tokens
  let sideGrossTradeAmt ← readOptional [49, 48, 55, 50] tokens
  let orderCategory ← readOptional [49, 49, 49, 53] tokens
  let sideLiquidityInd ← readOptional [49, 52, 52, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let clOrdID ← readOptional [49, 49] tokens
  let ordType ← readOptional [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let leavesQty ← readOptional [49, 53, 49] tokens
  let cumQty ← readOptional [49, 52] tokens
  let noOrderAttributes ← readGroup [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.decode tokens
  let freeText2 ← readOptional [50, 53, 48, 48, 56] tokens
  let freeText4 ← readOptional [50, 53, 49, 48, 55] tokens
  let orderIDSfx ← readOptional [50, 53, 49, 48, 56] tokens
  pure { side, sideTradeReportID, sideTradeID, noPartyIDs, partyIDClearingUnit, partyIDSettlementUnit, account, noClearingInstructions, numDaysInterest, accruedInterestAmt, settlCurrAmt, settlCurrFxRate, freeText1, sideGrossTradeAmt, orderCategory, sideLiquidityInd, orderID, clOrdID, ordType, price, leavesQty, cumQty, noOrderAttributes, freeText2, freeText4, orderIDSfx }

theorem NoSides.decode_agrees (record : NoSides) (tokens : List Token)
    (agrees : ∀ tags ∈ NoSides.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoSides.decode tokens = some record := by
  have distinct : NoSides.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have sideTradeReportID := readOptional_part [49, 48, 48, 53] record.sideTradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have sideTradeID := readOptional_part [49, 53, 48, 54] record.sideTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partyIDClearingUnit := readOptional_part [50, 53, 48, 50, 55] record.partyIDClearingUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have partyIDSettlementUnit := readOptional_part [50, 53, 49, 50, 48] record.partyIDSettlementUnit tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have noClearingInstructions := readGroup_part [53, 55, 54] [53, 55, 55] NoClearingInstructions.members NoClearingInstructions.encode NoClearingInstructions.within NoClearingInstructions.decode NoClearingInstructions.decode_encode NoClearingInstructions.led record.noClearingInstructions tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have numDaysInterest := readOptional_part [49, 53, 55] record.numDaysInterest tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have accruedInterestAmt := readOptional_part [49, 53, 57] record.accruedInterestAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have settlCurrAmt := readOptional_part [49, 49, 57] record.settlCurrAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have settlCurrFxRate := readOptional_part [49, 53, 53] record.settlCurrFxRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have freeText1 := readOptional_part [50, 53, 48, 48, 55] record.freeText1 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have sideGrossTradeAmt := readOptional_part [49, 48, 55, 50] record.sideGrossTradeAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have orderCategory := readOptional_part [49, 49, 49, 53] record.orderCategory tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have sideLiquidityInd := readOptional_part [49, 52, 52, 52] record.sideLiquidityInd tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have ordType := readOptional_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have leavesQty := readOptional_part [49, 53, 49] record.leavesQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have cumQty := readOptional_part [49, 52] record.cumQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have noOrderAttributes := readGroup_part [50, 53, 57, 51] [50, 53, 57, 52] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within NoOrderAttributes.decode NoOrderAttributes.decode_encode NoOrderAttributes.led record.noOrderAttributes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have freeText2 := readOptional_part [50, 53, 48, 48, 56] record.freeText2 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have freeText4 := readOptional_part [50, 53, 49, 48, 55] record.freeText4 tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have orderIDSfx := readOptional_part [50, 53, 49, 48, 56] record.orderIDSfx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  simp only [NoSides.decode, side, sideTradeReportID, sideTradeID, noPartyIDs, partyIDClearingUnit, partyIDSettlementUnit, account, noClearingInstructions, numDaysInterest, accruedInterestAmt, settlCurrAmt, settlCurrFxRate, freeText1, sideGrossTradeAmt, orderCategory, sideLiquidityInd, orderID, clOrdID, ordType, price, leavesQty, cumQty, noOrderAttributes, freeText2, freeText4, orderIDSfx, some_bind] <;> rfl

theorem NoSides.taken (record : NoSides) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48, 53] record.sideTradeReportID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 53, 48, 54] record.sideTradeID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
      (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 50, 55] record.partyIDClearingUnit (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 50, 48] record.partyIDSettlementUnit (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
         (paired_cons pairing _ _ (paired_group pairing [53, 55, 54] NoClearingInstructions.members NoClearingInstructions.encode NoClearingInstructions.within (by decide) (by decide) NoClearingInstructions.taken record.noClearingInstructions)
          (paired_cons pairing _ _ (paired_optional pairing [49, 53, 55] record.numDaysInterest (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 53, 57] record.accruedInterestAmt (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 49, 57] record.settlCurrAmt (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 53, 53] record.settlCurrFxRate (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 48, 55] record.freeText1 (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 48, 55, 50] record.sideGrossTradeAmt (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49, 53] record.orderCategory (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 52, 52, 52] record.sideLiquidityInd (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [52, 48] record.ordType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [49, 53, 49] record.leavesQty (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [49, 52] record.cumQty (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_group pairing [50, 53, 57, 51] NoOrderAttributes.members NoOrderAttributes.encode NoOrderAttributes.within (by decide) (by decide) NoOrderAttributes.taken record.noOrderAttributes)
                         (paired_cons pairing _ _ (paired_optional pairing [50, 53, 48, 48, 56] record.freeText2 (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 48, 55] record.freeText4 (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 48, 56] record.orderIDSfx (by decide) (by decide))
                            (paired_none pairing))))))))))))))))))))))))))

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
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  noRegulatoryTradeIDs : List NoRegulatoryTradeIDs  -- tag 1907
  noSRQSRelatedTradeIDs : List NoSRQSRelatedTradeIDs  -- tag 25174
  noRootPartyIDs : List NoRootPartyIDs  -- tag 1116
  noSides : List NoSides  -- tag 552
  currency : Terminated 1  -- tag 15
  lastMkt : Terminated 1  -- tag 30
  lastPx : Terminated 1  -- tag 31
  lastQty : Terminated 1  -- tag 32
  settlDate : Terminated 1  -- tag 64
  tradeDate : Terminated 1  -- tag 75
  settlCurrency : Terminated 1  -- tag 120
  tradeReportID : Terminated 1  -- tag 571
  matchType : Option (Terminated 1)  -- tag 574
  trdType : Terminated 1  -- tag 828
  transferReason : Terminated 1  -- tag 830
  tradeReportType : Terminated 1  -- tag 856
  trdMatchID : Option (Terminated 1)  -- tag 880
  tradeID : Terminated 1  -- tag 1003
  messageEventSource : Terminated 1  -- tag 1011
  origTradeID : Option (Terminated 1)  -- tag 1126
  tradePublishIndicator : Option (Terminated 1)  -- tag 1390
  orderOrigination : Option (Terminated 1)  -- tag 1724
  tradingCapacity : Option (Terminated 1)  -- tag 1815
  packageID : Option (Terminated 1)  -- tag 2489
  tradeNumber : Option (Terminated 1)  -- tag 2490
  matchSubType : Option (Terminated 1)  -- tag 28610
  negotiationID : Option (Terminated 1)  -- tag 28758
  uTransactTime : Terminated 1  -- tag 30060
  transactionCostCode : Option (Terminated 1)  -- tag 9473
  transactionCostAmt : Option (Terminated 1)  -- tag 9476
  tradePlatform : Option (Terminated 1)  -- tag 25160
  transBkdTime : Option (Terminated 1)  -- tag 483

def TradeCaptureReport.parts (record : TradeCaptureReport) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.group [49, 57, 48, 55] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within record.noRegulatoryTradeIDs,
   Part.group [50, 53, 49, 55, 52] NoSRQSRelatedTradeIDs.members NoSRQSRelatedTradeIDs.encode NoSRQSRelatedTradeIDs.within record.noSRQSRelatedTradeIDs,
   Part.group [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within record.noRootPartyIDs,
   Part.group [53, 53, 50] NoSides.members NoSides.encode NoSides.within record.noSides,
   Part.required [49, 53] record.currency,
   Part.required [51, 48] record.lastMkt,
   Part.required [51, 49] record.lastPx,
   Part.required [51, 50] record.lastQty,
   Part.required [54, 52] record.settlDate,
   Part.required [55, 53] record.tradeDate,
   Part.required [49, 50, 48] record.settlCurrency,
   Part.required [53, 55, 49] record.tradeReportID,
   Part.optional [53, 55, 52] record.matchType,
   Part.required [56, 50, 56] record.trdType,
   Part.required [56, 51, 48] record.transferReason,
   Part.required [56, 53, 54] record.tradeReportType,
   Part.optional [56, 56, 48] record.trdMatchID,
   Part.required [49, 48, 48, 51] record.tradeID,
   Part.required [49, 48, 49, 49] record.messageEventSource,
   Part.optional [49, 49, 50, 54] record.origTradeID,
   Part.optional [49, 51, 57, 48] record.tradePublishIndicator,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [49, 56, 49, 53] record.tradingCapacity,
   Part.optional [50, 52, 56, 57] record.packageID,
   Part.optional [50, 52, 57, 48] record.tradeNumber,
   Part.optional [50, 56, 54, 49, 48] record.matchSubType,
   Part.optional [50, 56, 55, 53, 56] record.negotiationID,
   Part.required [51, 48, 48, 54, 48] record.uTransactTime,
   Part.optional [57, 52, 55, 51] record.transactionCostCode,
   Part.optional [57, 52, 55, 54] record.transactionCostAmt,
   Part.optional [50, 53, 49, 54, 48] record.tradePlatform,
   Part.optional [52, 56, 51] record.transBkdTime]

def TradeCaptureReport.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [49, 57, 48, 55] :: NoRegulatoryTradeIDs.members, [50, 53, 49, 55, 52] :: NoSRQSRelatedTradeIDs.members, [49, 49, 49, 54] :: NoRootPartyIDs.members, [53, 53, 50] :: NoSides.members, [[49, 53]], [[51, 48]], [[51, 49]], [[51, 50]], [[54, 52]], [[55, 53]], [[49, 50, 48]], [[53, 55, 49]], [[53, 55, 52]], [[56, 50, 56]], [[56, 51, 48]], [[56, 53, 54]], [[56, 56, 48]], [[49, 48, 48, 51]], [[49, 48, 49, 49]], [[49, 49, 50, 54]], [[49, 51, 57, 48]], [[49, 55, 50, 52]], [[49, 56, 49, 53]], [[50, 52, 56, 57]], [[50, 52, 57, 48]], [[50, 56, 54, 49, 48]], [[50, 56, 55, 53, 56]], [[51, 48, 48, 54, 48]], [[57, 52, 55, 51]], [[57, 52, 55, 54]], [[50, 53, 49, 54, 48]], [[52, 56, 51]]]

theorem TradeCaptureReport.shape (record : TradeCaptureReport) : record.parts.map Part.tags = TradeCaptureReport.tags := rfl

def TradeCaptureReport.decode (tokens : List Token) : Option TradeCaptureReport := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let noRegulatoryTradeIDs ← readGroup [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.decode tokens
  let noSRQSRelatedTradeIDs ← readGroup [50, 53, 49, 55, 52] [50, 53, 49, 53, 50] NoSRQSRelatedTradeIDs.members NoSRQSRelatedTradeIDs.decode tokens
  let noRootPartyIDs ← readGroup [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.decode tokens
  let noSides ← readGroup [53, 53, 50] [53, 52] NoSides.members NoSides.decode tokens
  let currency ← readRequired [49, 53] tokens
  let lastMkt ← readRequired [51, 48] tokens
  let lastPx ← readRequired [51, 49] tokens
  let lastQty ← readRequired [51, 50] tokens
  let settlDate ← readRequired [54, 52] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let settlCurrency ← readRequired [49, 50, 48] tokens
  let tradeReportID ← readRequired [53, 55, 49] tokens
  let matchType ← readOptional [53, 55, 52] tokens
  let trdType ← readRequired [56, 50, 56] tokens
  let transferReason ← readRequired [56, 51, 48] tokens
  let tradeReportType ← readRequired [56, 53, 54] tokens
  let trdMatchID ← readOptional [56, 56, 48] tokens
  let tradeID ← readRequired [49, 48, 48, 51] tokens
  let messageEventSource ← readRequired [49, 48, 49, 49] tokens
  let origTradeID ← readOptional [49, 49, 50, 54] tokens
  let tradePublishIndicator ← readOptional [49, 51, 57, 48] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let tradingCapacity ← readOptional [49, 56, 49, 53] tokens
  let packageID ← readOptional [50, 52, 56, 57] tokens
  let tradeNumber ← readOptional [50, 52, 57, 48] tokens
  let matchSubType ← readOptional [50, 56, 54, 49, 48] tokens
  let negotiationID ← readOptional [50, 56, 55, 53, 56] tokens
  let uTransactTime ← readRequired [51, 48, 48, 54, 48] tokens
  let transactionCostCode ← readOptional [57, 52, 55, 51] tokens
  let transactionCostAmt ← readOptional [57, 52, 55, 54] tokens
  let tradePlatform ← readOptional [50, 53, 49, 54, 48] tokens
  let transBkdTime ← readOptional [52, 56, 51] tokens
  pure { symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noRegulatoryTradeIDs, noSRQSRelatedTradeIDs, noRootPartyIDs, noSides, currency, lastMkt, lastPx, lastQty, settlDate, tradeDate, settlCurrency, tradeReportID, matchType, trdType, transferReason, tradeReportType, trdMatchID, tradeID, messageEventSource, origTradeID, tradePublishIndicator, orderOrigination, tradingCapacity, packageID, tradeNumber, matchSubType, negotiationID, uTransactTime, transactionCostCode, transactionCostAmt, tradePlatform, transBkdTime }

theorem TradeCaptureReport.decode_agrees (record : TradeCaptureReport) (tokens : List Token)
    (agrees : ∀ tags ∈ TradeCaptureReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradeCaptureReport.decode tokens = some record := by
  have distinct : TradeCaptureReport.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noRegulatoryTradeIDs := readGroup_part [49, 57, 48, 55] [49, 57, 48, 51] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within NoRegulatoryTradeIDs.decode NoRegulatoryTradeIDs.decode_encode NoRegulatoryTradeIDs.led record.noRegulatoryTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noSRQSRelatedTradeIDs := readGroup_part [50, 53, 49, 55, 52] [50, 53, 49, 53, 50] NoSRQSRelatedTradeIDs.members NoSRQSRelatedTradeIDs.encode NoSRQSRelatedTradeIDs.within NoSRQSRelatedTradeIDs.decode NoSRQSRelatedTradeIDs.decode_encode NoSRQSRelatedTradeIDs.led record.noSRQSRelatedTradeIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noRootPartyIDs := readGroup_part [49, 49, 49, 54] [49, 49, 49, 55] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within NoRootPartyIDs.decode NoRootPartyIDs.decode_encode NoRootPartyIDs.led record.noRootPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have noSides := readGroup_part [53, 53, 50] [53, 52] NoSides.members NoSides.encode NoSides.within NoSides.decode NoSides.decode_encode NoSides.led record.noSides tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have currency := readRequired_part [49, 53] record.currency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have lastMkt := readRequired_part [51, 48] record.lastMkt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have lastPx := readRequired_part [51, 49] record.lastPx tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have lastQty := readRequired_part [51, 50] record.lastQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have settlDate := readRequired_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have settlCurrency := readRequired_part [49, 50, 48] record.settlCurrency tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have tradeReportID := readRequired_part [53, 55, 49] record.tradeReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have matchType := readOptional_part [53, 55, 52] record.matchType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have trdType := readRequired_part [56, 50, 56] record.trdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have transferReason := readRequired_part [56, 51, 48] record.transferReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have tradeReportType := readRequired_part [56, 53, 54] record.tradeReportType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have trdMatchID := readOptional_part [56, 56, 48] record.trdMatchID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have tradeID := readRequired_part [49, 48, 48, 51] record.tradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have messageEventSource := readRequired_part [49, 48, 49, 49] record.messageEventSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have origTradeID := readOptional_part [49, 49, 50, 54] record.origTradeID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have tradePublishIndicator := readOptional_part [49, 51, 57, 48] record.tradePublishIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have tradingCapacity := readOptional_part [49, 56, 49, 53] record.tradingCapacity tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have packageID := readOptional_part [50, 52, 56, 57] record.packageID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have tradeNumber := readOptional_part [50, 52, 57, 48] record.tradeNumber tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have matchSubType := readOptional_part [50, 56, 54, 49, 48] record.matchSubType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have negotiationID := readOptional_part [50, 56, 55, 53, 56] record.negotiationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have uTransactTime := readRequired_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  have transactionCostCode := readOptional_part [57, 52, 55, 51] record.transactionCostCode tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 36 (by decide +kernel)))
  have transactionCostAmt := readOptional_part [57, 52, 55, 54] record.transactionCostAmt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 37 (by decide +kernel)))
  have tradePlatform := readOptional_part [50, 53, 49, 54, 48] record.tradePlatform tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 38 (by decide +kernel)))
  have transBkdTime := readOptional_part [52, 56, 51] record.transBkdTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 39 (by decide +kernel)))
  simp only [TradeCaptureReport.decode, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noRegulatoryTradeIDs, noSRQSRelatedTradeIDs, noRootPartyIDs, noSides, currency, lastMkt, lastPx, lastQty, settlDate, tradeDate, settlCurrency, tradeReportID, matchType, trdType, transferReason, tradeReportType, trdMatchID, tradeID, messageEventSource, origTradeID, tradePublishIndicator, orderOrigination, tradingCapacity, packageID, tradeNumber, matchSubType, negotiationID, uTransactTime, transactionCostCode, transactionCostAmt, tradePlatform, transBkdTime, some_bind] <;> rfl

theorem TradeCaptureReport.taken (record : TradeCaptureReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within (by decide) (by decide) NoSecurityAltID.taken record.noSecurityAltID)
      (paired_cons pairing _ _ (paired_optional pairing [50, 50, 51] record.couponRate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 48] record.deliveryType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [49, 57, 48, 55] NoRegulatoryTradeIDs.members NoRegulatoryTradeIDs.encode NoRegulatoryTradeIDs.within (by decide) (by decide) NoRegulatoryTradeIDs.taken record.noRegulatoryTradeIDs)
           (paired_cons pairing _ _ (paired_group pairing [50, 53, 49, 55, 52] NoSRQSRelatedTradeIDs.members NoSRQSRelatedTradeIDs.encode NoSRQSRelatedTradeIDs.within (by decide) (by decide) NoSRQSRelatedTradeIDs.taken record.noSRQSRelatedTradeIDs)
            (paired_cons pairing _ _ (paired_group pairing [49, 49, 49, 54] NoRootPartyIDs.members NoRootPartyIDs.encode NoRootPartyIDs.within (by decide) (by decide) NoRootPartyIDs.taken record.noRootPartyIDs)
             (paired_cons pairing _ _ (paired_group pairing [53, 53, 50] NoSides.members NoSides.encode NoSides.within (by decide) (by decide) NoSides.taken record.noSides)
              (paired_cons pairing _ _ (paired_required pairing [49, 53] record.currency (by decide) (by decide))
               (paired_cons pairing _ _ (paired_required pairing [51, 48] record.lastMkt (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [51, 49] record.lastPx (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [51, 50] record.lastQty (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [54, 52] record.settlDate (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [49, 50, 48] record.settlCurrency (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [53, 55, 49] record.tradeReportID (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [53, 55, 52] record.matchType (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [56, 50, 56] record.trdType (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [56, 51, 48] record.transferReason (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [56, 53, 54] record.tradeReportType (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [56, 56, 48] record.trdMatchID (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_required pairing [49, 48, 48, 51] record.tradeID (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_required pairing [49, 48, 49, 49] record.messageEventSource (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 50, 54] record.origTradeID (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [49, 51, 57, 48] record.tradePublishIndicator (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.orderOrigination (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [49, 56, 49, 53] record.tradingCapacity (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [50, 52, 56, 57] record.packageID (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [50, 52, 57, 48] record.tradeNumber (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [50, 56, 54, 49, 48] record.matchSubType (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 53, 56] record.negotiationID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_required pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
                                      (paired_cons pairing _ _ (paired_optional pairing [57, 52, 55, 51] record.transactionCostCode (by decide) (by decide))
                                       (paired_cons pairing _ _ (paired_optional pairing [57, 52, 55, 54] record.transactionCostAmt (by decide) (by decide))
                                        (paired_cons pairing _ _ (paired_optional pairing [50, 53, 49, 54, 48] record.tradePlatform (by decide) (by decide))
                                         (paired_cons pairing _ _ (paired_optional pairing [52, 56, 51] record.transBkdTime (by decide) (by decide))
                                          (paired_none pairing))))))))))))))))))))))))))))))))))))))))

structure TradingSessionStatus where
  text : Option (Terminated 1)  -- tag 58
  tradingSessionID : Terminated 1  -- tag 336
  tradSesEvent : Terminated 1  -- tag 1368
  tradSesStatus : Terminated 1  -- tag 340
  marketSegmentID : Option (Terminated 1)  -- tag 1300
  uTransactTime : Option (Terminated 1)  -- tag 30060
  uTradeDate : Option (Terminated 1)  -- tag 30075

def TradingSessionStatus.parts (record : TradingSessionStatus) : List Part :=
  [Part.optional [53, 56] record.text,
   Part.required [51, 51, 54] record.tradingSessionID,
   Part.required [49, 51, 54, 56] record.tradSesEvent,
   Part.required [51, 52, 48] record.tradSesStatus,
   Part.optional [49, 51, 48, 48] record.marketSegmentID,
   Part.optional [51, 48, 48, 54, 48] record.uTransactTime,
   Part.optional [51, 48, 48, 55, 53] record.uTradeDate]

def TradingSessionStatus.tags : List (List (List UInt8)) :=
  [[[53, 56]], [[51, 51, 54]], [[49, 51, 54, 56]], [[51, 52, 48]], [[49, 51, 48, 48]], [[51, 48, 48, 54, 48]], [[51, 48, 48, 55, 53]]]

theorem TradingSessionStatus.shape (record : TradingSessionStatus) : record.parts.map Part.tags = TradingSessionStatus.tags := rfl

def TradingSessionStatus.decode (tokens : List Token) : Option TradingSessionStatus := do
  let text ← readOptional [53, 56] tokens
  let tradingSessionID ← readRequired [51, 51, 54] tokens
  let tradSesEvent ← readRequired [49, 51, 54, 56] tokens
  let tradSesStatus ← readRequired [51, 52, 48] tokens
  let marketSegmentID ← readOptional [49, 51, 48, 48] tokens
  let uTransactTime ← readOptional [51, 48, 48, 54, 48] tokens
  let uTradeDate ← readOptional [51, 48, 48, 55, 53] tokens
  pure { text, tradingSessionID, tradSesEvent, tradSesStatus, marketSegmentID, uTransactTime, uTradeDate }

theorem TradingSessionStatus.decode_agrees (record : TradingSessionStatus) (tokens : List Token)
    (agrees : ∀ tags ∈ TradingSessionStatus.tags, select tags tokens = select tags (encodeParts record.parts)) :
    TradingSessionStatus.decode tokens = some record := by
  have distinct : TradingSessionStatus.tags.flatten.Nodup := by decide +kernel
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradingSessionID := readRequired_part [51, 51, 54] record.tradingSessionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have tradSesEvent := readRequired_part [49, 51, 54, 56] record.tradSesEvent tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have tradSesStatus := readRequired_part [51, 52, 48] record.tradSesStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have marketSegmentID := readOptional_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have uTransactTime := readOptional_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have uTradeDate := readOptional_part [51, 48, 48, 55, 53] record.uTradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  simp only [TradingSessionStatus.decode, text, tradingSessionID, tradSesEvent, tradSesStatus, marketSegmentID, uTransactTime, uTradeDate, some_bind] <;> rfl

theorem TradingSessionStatus.taken (record : TradingSessionStatus) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 51, 54] record.tradingSessionID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 56] record.tradSesEvent (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 52, 48] record.tradSesStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 51, 48, 48] record.marketSegmentID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 55, 53] record.uTradeDate (by decide) (by decide))
         (paired_none pairing)))))))

structure NoUsernames where
  username : Terminated 1  -- tag 553

def NoUsernames.parts (record : NoUsernames) : List Part :=
  [Part.required [53, 53, 51] record.username]

def NoUsernames.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]]]

theorem NoUsernames.shape (record : NoUsernames) : record.parts.map Part.tags = NoUsernames.tags := rfl

def NoUsernames.decode (tokens : List Token) : Option NoUsernames := do
  let username ← readRequired [53, 53, 51] tokens
  pure { username }

theorem NoUsernames.decode_agrees (record : NoUsernames) (tokens : List Token)
    (agrees : ∀ tags ∈ NoUsernames.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoUsernames.decode tokens = some record := by
  have distinct : NoUsernames.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoUsernames.decode, username, some_bind] <;> rfl

theorem NoUsernames.taken (record : NoUsernames) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
   (paired_none pairing)

def NoUsernames.members : List (List UInt8) := NoUsernames.tags.flatten

def NoUsernames.encode (entry : NoUsernames) : List Token := encodeParts entry.parts

theorem NoUsernames.decode_encode (entry : NoUsernames) : NoUsernames.decode entry.encode = some entry :=
  NoUsernames.decode_agrees entry _ (fun _ _ => rfl)

theorem NoUsernames.within (entry : NoUsernames) : ∀ token ∈ entry.encode, token.tag ∈ NoUsernames.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoUsernames.shape] at this

theorem NoUsernames.led (entry : NoUsernames) : Lead [53, 53, 51] entry.encode :=
  lead_parts [53, 53, 51] entry.username _ NoUsernames.tags.tail rfl (by decide +kernel)

structure UserNotification where
  noUsernames : List NoUsernames  -- tag 809
  text : Option (Terminated 1)  -- tag 58
  userStatus : Terminated 1  -- tag 926

def UserNotification.parts (record : UserNotification) : List Part :=
  [Part.group [56, 48, 57] NoUsernames.members NoUsernames.encode NoUsernames.within record.noUsernames,
   Part.optional [53, 56] record.text,
   Part.required [57, 50, 54] record.userStatus]

def UserNotification.tags : List (List (List UInt8)) :=
  [[56, 48, 57] :: NoUsernames.members, [[53, 56]], [[57, 50, 54]]]

theorem UserNotification.shape (record : UserNotification) : record.parts.map Part.tags = UserNotification.tags := rfl

def UserNotification.decode (tokens : List Token) : Option UserNotification := do
  let noUsernames ← readGroup [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.decode tokens
  let text ← readOptional [53, 56] tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  pure { noUsernames, text, userStatus }

theorem UserNotification.decode_agrees (record : UserNotification) (tokens : List Token)
    (agrees : ∀ tags ∈ UserNotification.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserNotification.decode tokens = some record := by
  have distinct : UserNotification.tags.flatten.Nodup := by decide +kernel
  have noUsernames := readGroup_part [56, 48, 57] [53, 53, 51] NoUsernames.members NoUsernames.encode NoUsernames.within NoUsernames.decode NoUsernames.decode_encode NoUsernames.led record.noUsernames tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [UserNotification.decode, noUsernames, text, userStatus, some_bind] <;> rfl

theorem UserNotification.taken (record : UserNotification) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [56, 48, 57] NoUsernames.members NoUsernames.encode NoUsernames.within (by decide) (by decide) NoUsernames.taken record.noUsernames)
   (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [57, 50, 54] record.userStatus (by decide) (by decide))
     (paired_none pairing)))

structure NoNotAffectedOrders where
  notAffectedOrderID : Terminated 1  -- tag 1371
  notAffOrigClOrdID : Option (Terminated 1)  -- tag 1372

def NoNotAffectedOrders.parts (record : NoNotAffectedOrders) : List Part :=
  [Part.required [49, 51, 55, 49] record.notAffectedOrderID,
   Part.optional [49, 51, 55, 50] record.notAffOrigClOrdID]

def NoNotAffectedOrders.tags : List (List (List UInt8)) :=
  [[[49, 51, 55, 49]], [[49, 51, 55, 50]]]

theorem NoNotAffectedOrders.shape (record : NoNotAffectedOrders) : record.parts.map Part.tags = NoNotAffectedOrders.tags := rfl

def NoNotAffectedOrders.decode (tokens : List Token) : Option NoNotAffectedOrders := do
  let notAffectedOrderID ← readRequired [49, 51, 55, 49] tokens
  let notAffOrigClOrdID ← readOptional [49, 51, 55, 50] tokens
  pure { notAffectedOrderID, notAffOrigClOrdID }

theorem NoNotAffectedOrders.decode_agrees (record : NoNotAffectedOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoNotAffectedOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoNotAffectedOrders.decode tokens = some record := by
  have distinct : NoNotAffectedOrders.tags.flatten.Nodup := by decide +kernel
  have notAffectedOrderID := readRequired_part [49, 51, 55, 49] record.notAffectedOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have notAffOrigClOrdID := readOptional_part [49, 51, 55, 50] record.notAffOrigClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoNotAffectedOrders.decode, notAffectedOrderID, notAffOrigClOrdID, some_bind] <;> rfl

theorem NoNotAffectedOrders.taken (record : NoNotAffectedOrders) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 51, 55, 49] record.notAffectedOrderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 51, 55, 50] record.notAffOrigClOrdID (by decide) (by decide))
    (paired_none pairing))

def NoNotAffectedOrders.members : List (List UInt8) := NoNotAffectedOrders.tags.flatten

def NoNotAffectedOrders.encode (entry : NoNotAffectedOrders) : List Token := encodeParts entry.parts

theorem NoNotAffectedOrders.decode_encode (entry : NoNotAffectedOrders) : NoNotAffectedOrders.decode entry.encode = some entry :=
  NoNotAffectedOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoNotAffectedOrders.within (entry : NoNotAffectedOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoNotAffectedOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoNotAffectedOrders.shape] at this

theorem NoNotAffectedOrders.led (entry : NoNotAffectedOrders) : Lead [49, 51, 55, 49] entry.encode :=
  lead_parts [49, 51, 55, 49] entry.notAffectedOrderID _ NoNotAffectedOrders.tags.tail rfl (by decide +kernel)

structure NoAffectedOrders where
  affectedOrderID : Terminated 1  -- tag 535
  affectedOrigClOrdID : Option (Terminated 1)  -- tag 1824

def NoAffectedOrders.parts (record : NoAffectedOrders) : List Part :=
  [Part.required [53, 51, 53] record.affectedOrderID,
   Part.optional [49, 56, 50, 52] record.affectedOrigClOrdID]

def NoAffectedOrders.tags : List (List (List UInt8)) :=
  [[[53, 51, 53]], [[49, 56, 50, 52]]]

theorem NoAffectedOrders.shape (record : NoAffectedOrders) : record.parts.map Part.tags = NoAffectedOrders.tags := rfl

def NoAffectedOrders.decode (tokens : List Token) : Option NoAffectedOrders := do
  let affectedOrderID ← readRequired [53, 51, 53] tokens
  let affectedOrigClOrdID ← readOptional [49, 56, 50, 52] tokens
  pure { affectedOrderID, affectedOrigClOrdID }

theorem NoAffectedOrders.decode_agrees (record : NoAffectedOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoAffectedOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoAffectedOrders.decode tokens = some record := by
  have distinct : NoAffectedOrders.tags.flatten.Nodup := by decide +kernel
  have affectedOrderID := readRequired_part [53, 51, 53] record.affectedOrderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have affectedOrigClOrdID := readOptional_part [49, 56, 50, 52] record.affectedOrigClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoAffectedOrders.decode, affectedOrderID, affectedOrigClOrdID, some_bind] <;> rfl

theorem NoAffectedOrders.taken (record : NoAffectedOrders) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 51, 53] record.affectedOrderID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 56, 50, 52] record.affectedOrigClOrdID (by decide) (by decide))
    (paired_none pairing))

def NoAffectedOrders.members : List (List UInt8) := NoAffectedOrders.tags.flatten

def NoAffectedOrders.encode (entry : NoAffectedOrders) : List Token := encodeParts entry.parts

theorem NoAffectedOrders.decode_encode (entry : NoAffectedOrders) : NoAffectedOrders.decode entry.encode = some entry :=
  NoAffectedOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoAffectedOrders.within (entry : NoAffectedOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoAffectedOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoAffectedOrders.shape] at this

theorem NoAffectedOrders.led (entry : NoAffectedOrders) : Lead [53, 51, 53] entry.encode :=
  lead_parts [53, 51, 53] entry.affectedOrderID _ NoAffectedOrders.tags.tail rfl (by decide +kernel)

structure UserOrderMassActionReport where
  symbol : Terminated 1  -- tag 55
  securityID : Option (Terminated 1)  -- tag 48
  securityIDSource : Option (Terminated 1)  -- tag 22
  noSecurityAltID : List NoSecurityAltID  -- tag 454
  couponRate : Option (Terminated 1)  -- tag 223
  deliveryType : Option (Terminated 1)  -- tag 28890
  lastCouponDeviationIndicator : Option (Terminated 1)  -- tag 28896
  refinancingEligibilityIndicator : Option (Terminated 1)  -- tag 28897
  noPartyIDs : List NoPartyIDs  -- tag 453
  noNotAffectedOrders : List NoNotAffectedOrders  -- tag 1370
  noAffectedOrders : List NoAffectedOrders  -- tag 534
  clOrdID : Option (Terminated 1)  -- tag 11
  side : Option (Terminated 1)  -- tag 54
  price : Option (Terminated 1)  -- tag 44
  uExecInst : Option (Terminated 1)  -- tag 30018
  massActionReportID : Terminated 1  -- tag 1369
  massActionReason : Terminated 1  -- tag 28721

def UserOrderMassActionReport.parts (record : UserOrderMassActionReport) : List Part :=
  [Part.required [53, 53] record.symbol,
   Part.optional [52, 56] record.securityID,
   Part.optional [50, 50] record.securityIDSource,
   Part.group [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within record.noSecurityAltID,
   Part.optional [50, 50, 51] record.couponRate,
   Part.optional [50, 56, 56, 57, 48] record.deliveryType,
   Part.optional [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator,
   Part.optional [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator,
   Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 51, 55, 48] NoNotAffectedOrders.members NoNotAffectedOrders.encode NoNotAffectedOrders.within record.noNotAffectedOrders,
   Part.group [53, 51, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within record.noAffectedOrders,
   Part.optional [49, 49] record.clOrdID,
   Part.optional [53, 52] record.side,
   Part.optional [52, 52] record.price,
   Part.optional [51, 48, 48, 49, 56] record.uExecInst,
   Part.required [49, 51, 54, 57] record.massActionReportID,
   Part.required [50, 56, 55, 50, 49] record.massActionReason]

def UserOrderMassActionReport.tags : List (List (List UInt8)) :=
  [[[53, 53]], [[52, 56]], [[50, 50]], [52, 53, 52] :: NoSecurityAltID.members, [[50, 50, 51]], [[50, 56, 56, 57, 48]], [[50, 56, 56, 57, 54]], [[50, 56, 56, 57, 55]], [52, 53, 51] :: NoPartyIDs.members, [49, 51, 55, 48] :: NoNotAffectedOrders.members, [53, 51, 52] :: NoAffectedOrders.members, [[49, 49]], [[53, 52]], [[52, 52]], [[51, 48, 48, 49, 56]], [[49, 51, 54, 57]], [[50, 56, 55, 50, 49]]]

theorem UserOrderMassActionReport.shape (record : UserOrderMassActionReport) : record.parts.map Part.tags = UserOrderMassActionReport.tags := rfl

def UserOrderMassActionReport.decode (tokens : List Token) : Option UserOrderMassActionReport := do
  let symbol ← readRequired [53, 53] tokens
  let securityID ← readOptional [52, 56] tokens
  let securityIDSource ← readOptional [50, 50] tokens
  let noSecurityAltID ← readGroup [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.decode tokens
  let couponRate ← readOptional [50, 50, 51] tokens
  let deliveryType ← readOptional [50, 56, 56, 57, 48] tokens
  let lastCouponDeviationIndicator ← readOptional [50, 56, 56, 57, 54] tokens
  let refinancingEligibilityIndicator ← readOptional [50, 56, 56, 57, 55] tokens
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noNotAffectedOrders ← readGroup [49, 51, 55, 48] [49, 51, 55, 49] NoNotAffectedOrders.members NoNotAffectedOrders.decode tokens
  let noAffectedOrders ← readGroup [53, 51, 52] [53, 51, 53] NoAffectedOrders.members NoAffectedOrders.decode tokens
  let clOrdID ← readOptional [49, 49] tokens
  let side ← readOptional [53, 52] tokens
  let price ← readOptional [52, 52] tokens
  let uExecInst ← readOptional [51, 48, 48, 49, 56] tokens
  let massActionReportID ← readRequired [49, 51, 54, 57] tokens
  let massActionReason ← readRequired [50, 56, 55, 50, 49] tokens
  pure { symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noPartyIDs, noNotAffectedOrders, noAffectedOrders, clOrdID, side, price, uExecInst, massActionReportID, massActionReason }

theorem UserOrderMassActionReport.decode_agrees (record : UserOrderMassActionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ UserOrderMassActionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserOrderMassActionReport.decode tokens = some record := by
  have distinct : UserOrderMassActionReport.tags.flatten.Nodup := by decide +kernel
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have securityID := readOptional_part [52, 56] record.securityID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have securityIDSource := readOptional_part [50, 50] record.securityIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have noSecurityAltID := readGroup_part [52, 53, 52] [52, 53, 53] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within NoSecurityAltID.decode NoSecurityAltID.decode_encode NoSecurityAltID.led record.noSecurityAltID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have couponRate := readOptional_part [50, 50, 51] record.couponRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have deliveryType := readOptional_part [50, 56, 56, 57, 48] record.deliveryType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have lastCouponDeviationIndicator := readOptional_part [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have refinancingEligibilityIndicator := readOptional_part [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have noNotAffectedOrders := readGroup_part [49, 51, 55, 48] [49, 51, 55, 49] NoNotAffectedOrders.members NoNotAffectedOrders.encode NoNotAffectedOrders.within NoNotAffectedOrders.decode NoNotAffectedOrders.decode_encode NoNotAffectedOrders.led record.noNotAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have noAffectedOrders := readGroup_part [53, 51, 52] [53, 51, 53] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within NoAffectedOrders.decode NoAffectedOrders.decode_encode NoAffectedOrders.led record.noAffectedOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have clOrdID := readOptional_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have side := readOptional_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have uExecInst := readOptional_part [51, 48, 48, 49, 56] record.uExecInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have massActionReportID := readRequired_part [49, 51, 54, 57] record.massActionReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have massActionReason := readRequired_part [50, 56, 55, 50, 49] record.massActionReason tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [UserOrderMassActionReport.decode, symbol, securityID, securityIDSource, noSecurityAltID, couponRate, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, noPartyIDs, noNotAffectedOrders, noAffectedOrders, clOrdID, side, price, uExecInst, massActionReportID, massActionReason, some_bind] <;> rfl

theorem UserOrderMassActionReport.taken (record : UserOrderMassActionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 56] record.securityID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 50] record.securityIDSource (by decide) (by decide))
     (paired_cons pairing _ _ (paired_group pairing [52, 53, 52] NoSecurityAltID.members NoSecurityAltID.encode NoSecurityAltID.within (by decide) (by decide) NoSecurityAltID.taken record.noSecurityAltID)
      (paired_cons pairing _ _ (paired_optional pairing [50, 50, 51] record.couponRate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 48] record.deliveryType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 54] record.lastCouponDeviationIndicator (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 57, 55] record.refinancingEligibilityIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
           (paired_cons pairing _ _ (paired_group pairing [49, 51, 55, 48] NoNotAffectedOrders.members NoNotAffectedOrders.encode NoNotAffectedOrders.within (by decide) (by decide) NoNotAffectedOrders.taken record.noNotAffectedOrders)
            (paired_cons pairing _ _ (paired_group pairing [53, 51, 52] NoAffectedOrders.members NoAffectedOrders.encode NoAffectedOrders.within (by decide) (by decide) NoAffectedOrders.taken record.noAffectedOrders)
             (paired_cons pairing _ _ (paired_optional pairing [49, 49] record.clOrdID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [53, 52] record.side (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [51, 48, 48, 49, 56] record.uExecInst (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_required pairing [49, 51, 54, 57] record.massActionReportID (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 50, 49] record.massActionReason (by decide) (by decide))
                   (paired_none pairing)))))))))))))))))

structure NoRequestingPartyIDs where
  requestingPartyID : Terminated 1  -- tag 1658
  requestingPartyIDSource : Terminated 1  -- tag 1659
  requestingPartyRole : Terminated 1  -- tag 1660

def NoRequestingPartyIDs.parts (record : NoRequestingPartyIDs) : List Part :=
  [Part.required [49, 54, 53, 56] record.requestingPartyID,
   Part.required [49, 54, 53, 57] record.requestingPartyIDSource,
   Part.required [49, 54, 54, 48] record.requestingPartyRole]

def NoRequestingPartyIDs.tags : List (List (List UInt8)) :=
  [[[49, 54, 53, 56]], [[49, 54, 53, 57]], [[49, 54, 54, 48]]]

theorem NoRequestingPartyIDs.shape (record : NoRequestingPartyIDs) : record.parts.map Part.tags = NoRequestingPartyIDs.tags := rfl

def NoRequestingPartyIDs.decode (tokens : List Token) : Option NoRequestingPartyIDs := do
  let requestingPartyID ← readRequired [49, 54, 53, 56] tokens
  let requestingPartyIDSource ← readRequired [49, 54, 53, 57] tokens
  let requestingPartyRole ← readRequired [49, 54, 54, 48] tokens
  pure { requestingPartyID, requestingPartyIDSource, requestingPartyRole }

theorem NoRequestingPartyIDs.decode_agrees (record : NoRequestingPartyIDs) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRequestingPartyIDs.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRequestingPartyIDs.decode tokens = some record := by
  have distinct : NoRequestingPartyIDs.tags.flatten.Nodup := by decide +kernel
  have requestingPartyID := readRequired_part [49, 54, 53, 56] record.requestingPartyID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have requestingPartyIDSource := readRequired_part [49, 54, 53, 57] record.requestingPartyIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have requestingPartyRole := readRequired_part [49, 54, 54, 48] record.requestingPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [NoRequestingPartyIDs.decode, requestingPartyID, requestingPartyIDSource, requestingPartyRole, some_bind] <;> rfl

theorem NoRequestingPartyIDs.taken (record : NoRequestingPartyIDs) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 53, 56] record.requestingPartyID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54, 53, 57] record.requestingPartyIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 54, 54, 48] record.requestingPartyRole (by decide) (by decide))
     (paired_none pairing)))

def NoRequestingPartyIDs.members : List (List UInt8) := NoRequestingPartyIDs.tags.flatten

def NoRequestingPartyIDs.encode (entry : NoRequestingPartyIDs) : List Token := encodeParts entry.parts

theorem NoRequestingPartyIDs.decode_encode (entry : NoRequestingPartyIDs) : NoRequestingPartyIDs.decode entry.encode = some entry :=
  NoRequestingPartyIDs.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRequestingPartyIDs.within (entry : NoRequestingPartyIDs) : ∀ token ∈ entry.encode, token.tag ∈ NoRequestingPartyIDs.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRequestingPartyIDs.shape] at this

theorem NoRequestingPartyIDs.led (entry : NoRequestingPartyIDs) : Lead [49, 54, 53, 56] entry.encode :=
  lead_parts [49, 54, 53, 56] entry.requestingPartyID _ NoRequestingPartyIDs.tags.tail rfl (by decide +kernel)

structure UserPartyActionReport where
  noPartyIDs : List NoPartyIDs  -- tag 453
  noRequestingPartyIDs : List NoRequestingPartyIDs  -- tag 1657
  partyActionType : Option (Terminated 1)  -- tag 2329
  uTransactTime : Terminated 1  -- tag 30060
  tradeDate : Terminated 1  -- tag 75
  marketID : Terminated 1  -- tag 1301

def UserPartyActionReport.parts (record : UserPartyActionReport) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.group [49, 54, 53, 55] NoRequestingPartyIDs.members NoRequestingPartyIDs.encode NoRequestingPartyIDs.within record.noRequestingPartyIDs,
   Part.optional [50, 51, 50, 57] record.partyActionType,
   Part.required [51, 48, 48, 54, 48] record.uTransactTime,
   Part.required [55, 53] record.tradeDate,
   Part.required [49, 51, 48, 49] record.marketID]

def UserPartyActionReport.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [49, 54, 53, 55] :: NoRequestingPartyIDs.members, [[50, 51, 50, 57]], [[51, 48, 48, 54, 48]], [[55, 53]], [[49, 51, 48, 49]]]

theorem UserPartyActionReport.shape (record : UserPartyActionReport) : record.parts.map Part.tags = UserPartyActionReport.tags := rfl

def UserPartyActionReport.decode (tokens : List Token) : Option UserPartyActionReport := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let noRequestingPartyIDs ← readGroup [49, 54, 53, 55] [49, 54, 53, 56] NoRequestingPartyIDs.members NoRequestingPartyIDs.decode tokens
  let partyActionType ← readOptional [50, 51, 50, 57] tokens
  let uTransactTime ← readRequired [51, 48, 48, 54, 48] tokens
  let tradeDate ← readRequired [55, 53] tokens
  let marketID ← readRequired [49, 51, 48, 49] tokens
  pure { noPartyIDs, noRequestingPartyIDs, partyActionType, uTransactTime, tradeDate, marketID }

theorem UserPartyActionReport.decode_agrees (record : UserPartyActionReport) (tokens : List Token)
    (agrees : ∀ tags ∈ UserPartyActionReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserPartyActionReport.decode tokens = some record := by
  have distinct : UserPartyActionReport.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRequestingPartyIDs := readGroup_part [49, 54, 53, 55] [49, 54, 53, 56] NoRequestingPartyIDs.members NoRequestingPartyIDs.encode NoRequestingPartyIDs.within NoRequestingPartyIDs.decode NoRequestingPartyIDs.decode_encode NoRequestingPartyIDs.led record.noRequestingPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyActionType := readOptional_part [50, 51, 50, 57] record.partyActionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have uTransactTime := readRequired_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [UserPartyActionReport.decode, noPartyIDs, noRequestingPartyIDs, partyActionType, uTransactTime, tradeDate, marketID, some_bind] <;> rfl

theorem UserPartyActionReport.taken (record : UserPartyActionReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_group pairing [49, 54, 53, 55] NoRequestingPartyIDs.members NoRequestingPartyIDs.encode NoRequestingPartyIDs.within (by decide) (by decide) NoRequestingPartyIDs.taken record.noRequestingPartyIDs)
    (paired_cons pairing _ _ (paired_optional pairing [50, 51, 50, 57] record.partyActionType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 51, 48, 49] record.marketID (by decide) (by decide))
        (paired_none pairing))))))

structure UserPartyEntitlementsUpdateReport where
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradeDate : Option (Terminated 1)  -- tag 75
  listUpdateAction : Option (Terminated 1)  -- tag 1324
  partyDetailStatus : Option (Terminated 1)  -- tag 1672
  uTransactTime : Terminated 1  -- tag 30060
  marketID : Terminated 1  -- tag 1301

def UserPartyEntitlementsUpdateReport.parts (record : UserPartyEntitlementsUpdateReport) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.optional [55, 53] record.tradeDate,
   Part.optional [49, 51, 50, 52] record.listUpdateAction,
   Part.optional [49, 54, 55, 50] record.partyDetailStatus,
   Part.required [51, 48, 48, 54, 48] record.uTransactTime,
   Part.required [49, 51, 48, 49] record.marketID]

def UserPartyEntitlementsUpdateReport.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[55, 53]], [[49, 51, 50, 52]], [[49, 54, 55, 50]], [[51, 48, 48, 54, 48]], [[49, 51, 48, 49]]]

theorem UserPartyEntitlementsUpdateReport.shape (record : UserPartyEntitlementsUpdateReport) : record.parts.map Part.tags = UserPartyEntitlementsUpdateReport.tags := rfl

def UserPartyEntitlementsUpdateReport.decode (tokens : List Token) : Option UserPartyEntitlementsUpdateReport := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradeDate ← readOptional [55, 53] tokens
  let listUpdateAction ← readOptional [49, 51, 50, 52] tokens
  let partyDetailStatus ← readOptional [49, 54, 55, 50] tokens
  let uTransactTime ← readRequired [51, 48, 48, 54, 48] tokens
  let marketID ← readRequired [49, 51, 48, 49] tokens
  pure { noPartyIDs, tradeDate, listUpdateAction, partyDetailStatus, uTransactTime, marketID }

theorem UserPartyEntitlementsUpdateReport.decode_agrees (record : UserPartyEntitlementsUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ UserPartyEntitlementsUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserPartyEntitlementsUpdateReport.decode tokens = some record := by
  have distinct : UserPartyEntitlementsUpdateReport.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeDate := readOptional_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have listUpdateAction := readOptional_part [49, 51, 50, 52] record.listUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyDetailStatus := readOptional_part [49, 54, 55, 50] record.partyDetailStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have uTransactTime := readRequired_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [UserPartyEntitlementsUpdateReport.decode, noPartyIDs, tradeDate, listUpdateAction, partyDetailStatus, uTransactTime, marketID, some_bind] <;> rfl

theorem UserPartyEntitlementsUpdateReport.taken (record : UserPartyEntitlementsUpdateReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_optional pairing [55, 53] record.tradeDate (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50, 52] record.listUpdateAction (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55, 50] record.partyDetailStatus (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 51, 48, 49] record.marketID (by decide) (by decide))
        (paired_none pairing))))))

structure NoPartyDetails where
  partyDetailID : Terminated 1  -- tag 1691
  partyDetailIDSource : Terminated 1  -- tag 1692
  partyDetailRole : Terminated 1  -- tag 1693
  partyDetailStatus : Terminated 1  -- tag 1672

def NoPartyDetails.parts (record : NoPartyDetails) : List Part :=
  [Part.required [49, 54, 57, 49] record.partyDetailID,
   Part.required [49, 54, 57, 50] record.partyDetailIDSource,
   Part.required [49, 54, 57, 51] record.partyDetailRole,
   Part.required [49, 54, 55, 50] record.partyDetailStatus]

def NoPartyDetails.tags : List (List (List UInt8)) :=
  [[[49, 54, 57, 49]], [[49, 54, 57, 50]], [[49, 54, 57, 51]], [[49, 54, 55, 50]]]

theorem NoPartyDetails.shape (record : NoPartyDetails) : record.parts.map Part.tags = NoPartyDetails.tags := rfl

def NoPartyDetails.decode (tokens : List Token) : Option NoPartyDetails := do
  let partyDetailID ← readRequired [49, 54, 57, 49] tokens
  let partyDetailIDSource ← readRequired [49, 54, 57, 50] tokens
  let partyDetailRole ← readRequired [49, 54, 57, 51] tokens
  let partyDetailStatus ← readRequired [49, 54, 55, 50] tokens
  pure { partyDetailID, partyDetailIDSource, partyDetailRole, partyDetailStatus }

theorem NoPartyDetails.decode_agrees (record : NoPartyDetails) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyDetails.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyDetails.decode tokens = some record := by
  have distinct : NoPartyDetails.tags.flatten.Nodup := by decide +kernel
  have partyDetailID := readRequired_part [49, 54, 57, 49] record.partyDetailID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have partyDetailIDSource := readRequired_part [49, 54, 57, 50] record.partyDetailIDSource tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have partyDetailRole := readRequired_part [49, 54, 57, 51] record.partyDetailRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have partyDetailStatus := readRequired_part [49, 54, 55, 50] record.partyDetailStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [NoPartyDetails.decode, partyDetailID, partyDetailIDSource, partyDetailRole, partyDetailStatus, some_bind] <;> rfl

theorem NoPartyDetails.taken (record : NoPartyDetails) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 49] record.partyDetailID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 50] record.partyDetailIDSource (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 54, 57, 51] record.partyDetailRole (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 54, 55, 50] record.partyDetailStatus (by decide) (by decide))
      (paired_none pairing))))

def NoPartyDetails.members : List (List UInt8) := NoPartyDetails.tags.flatten

def NoPartyDetails.encode (entry : NoPartyDetails) : List Token := encodeParts entry.parts

theorem NoPartyDetails.decode_encode (entry : NoPartyDetails) : NoPartyDetails.decode entry.encode = some entry :=
  NoPartyDetails.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyDetails.within (entry : NoPartyDetails) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyDetails.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyDetails.shape] at this

theorem NoPartyDetails.led (entry : NoPartyDetails) : Lead [49, 54, 57, 49] entry.encode :=
  lead_parts [49, 54, 57, 49] entry.partyDetailID _ NoPartyDetails.tags.tail rfl (by decide +kernel)

structure NoRiskLimitTypes where
  riskLimitType : Terminated 1  -- tag 1530
  riskLimitRequestingPartyRole : Terminated 1  -- tag 28776
  riskLimitViolationIndicator : Terminated 1  -- tag 28778
  riskLimitGroup : Option (Terminated 1)  -- tag 28775
  riskLimitAmount : Option (Terminated 1)  -- tag 1531
  activationDate : Option (Terminated 1)  -- tag 28905
  riskLimitOpenAmount : Option (Terminated 1)  -- tag 28784
  riskLimitNetPositionAmount : Option (Terminated 1)  -- tag 28785

def NoRiskLimitTypes.parts (record : NoRiskLimitTypes) : List Part :=
  [Part.required [49, 53, 51, 48] record.riskLimitType,
   Part.required [50, 56, 55, 55, 54] record.riskLimitRequestingPartyRole,
   Part.required [50, 56, 55, 55, 56] record.riskLimitViolationIndicator,
   Part.optional [50, 56, 55, 55, 53] record.riskLimitGroup,
   Part.optional [49, 53, 51, 49] record.riskLimitAmount,
   Part.optional [50, 56, 57, 48, 53] record.activationDate,
   Part.optional [50, 56, 55, 56, 52] record.riskLimitOpenAmount,
   Part.optional [50, 56, 55, 56, 53] record.riskLimitNetPositionAmount]

def NoRiskLimitTypes.tags : List (List (List UInt8)) :=
  [[[49, 53, 51, 48]], [[50, 56, 55, 55, 54]], [[50, 56, 55, 55, 56]], [[50, 56, 55, 55, 53]], [[49, 53, 51, 49]], [[50, 56, 57, 48, 53]], [[50, 56, 55, 56, 52]], [[50, 56, 55, 56, 53]]]

theorem NoRiskLimitTypes.shape (record : NoRiskLimitTypes) : record.parts.map Part.tags = NoRiskLimitTypes.tags := rfl

def NoRiskLimitTypes.decode (tokens : List Token) : Option NoRiskLimitTypes := do
  let riskLimitType ← readRequired [49, 53, 51, 48] tokens
  let riskLimitRequestingPartyRole ← readRequired [50, 56, 55, 55, 54] tokens
  let riskLimitViolationIndicator ← readRequired [50, 56, 55, 55, 56] tokens
  let riskLimitGroup ← readOptional [50, 56, 55, 55, 53] tokens
  let riskLimitAmount ← readOptional [49, 53, 51, 49] tokens
  let activationDate ← readOptional [50, 56, 57, 48, 53] tokens
  let riskLimitOpenAmount ← readOptional [50, 56, 55, 56, 52] tokens
  let riskLimitNetPositionAmount ← readOptional [50, 56, 55, 56, 53] tokens
  pure { riskLimitType, riskLimitRequestingPartyRole, riskLimitViolationIndicator, riskLimitGroup, riskLimitAmount, activationDate, riskLimitOpenAmount, riskLimitNetPositionAmount }

theorem NoRiskLimitTypes.decode_agrees (record : NoRiskLimitTypes) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskLimitTypes.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskLimitTypes.decode tokens = some record := by
  have distinct : NoRiskLimitTypes.tags.flatten.Nodup := by decide +kernel
  have riskLimitType := readRequired_part [49, 53, 51, 48] record.riskLimitType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have riskLimitRequestingPartyRole := readRequired_part [50, 56, 55, 55, 54] record.riskLimitRequestingPartyRole tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have riskLimitViolationIndicator := readRequired_part [50, 56, 55, 55, 56] record.riskLimitViolationIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have riskLimitGroup := readOptional_part [50, 56, 55, 55, 53] record.riskLimitGroup tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have riskLimitAmount := readOptional_part [49, 53, 51, 49] record.riskLimitAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have activationDate := readOptional_part [50, 56, 57, 48, 53] record.activationDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have riskLimitOpenAmount := readOptional_part [50, 56, 55, 56, 52] record.riskLimitOpenAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have riskLimitNetPositionAmount := readOptional_part [50, 56, 55, 56, 53] record.riskLimitNetPositionAmount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [NoRiskLimitTypes.decode, riskLimitType, riskLimitRequestingPartyRole, riskLimitViolationIndicator, riskLimitGroup, riskLimitAmount, activationDate, riskLimitOpenAmount, riskLimitNetPositionAmount, some_bind] <;> rfl

theorem NoRiskLimitTypes.taken (record : NoRiskLimitTypes) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 53, 51, 48] record.riskLimitType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 55, 54] record.riskLimitRequestingPartyRole (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 56, 55, 55, 56] record.riskLimitViolationIndicator (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 55, 53] record.riskLimitGroup (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [49, 53, 51, 49] record.riskLimitAmount (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [50, 56, 57, 48, 53] record.activationDate (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 56, 52] record.riskLimitOpenAmount (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 55, 56, 53] record.riskLimitNetPositionAmount (by decide) (by decide))
          (paired_none pairing))))))))

def NoRiskLimitTypes.members : List (List UInt8) := NoRiskLimitTypes.tags.flatten

def NoRiskLimitTypes.encode (entry : NoRiskLimitTypes) : List Token := encodeParts entry.parts

theorem NoRiskLimitTypes.decode_encode (entry : NoRiskLimitTypes) : NoRiskLimitTypes.decode entry.encode = some entry :=
  NoRiskLimitTypes.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskLimitTypes.within (entry : NoRiskLimitTypes) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskLimitTypes.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskLimitTypes.shape] at this

theorem NoRiskLimitTypes.led (entry : NoRiskLimitTypes) : Lead [49, 53, 51, 48] entry.encode :=
  lead_parts [49, 53, 51, 48] entry.riskLimitType _ NoRiskLimitTypes.tags.tail rfl (by decide +kernel)

structure NoRiskLimits where
  noRiskLimitTypes : List NoRiskLimitTypes  -- tag 1529

def NoRiskLimits.parts (record : NoRiskLimits) : List Part :=
  [Part.groupLed [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within record.noRiskLimitTypes]

def NoRiskLimits.tags : List (List (List UInt8)) :=
  [[49, 53, 50, 57] :: NoRiskLimitTypes.members]

theorem NoRiskLimits.shape (record : NoRiskLimits) : record.parts.map Part.tags = NoRiskLimits.tags := rfl

def NoRiskLimits.decode (tokens : List Token) : Option NoRiskLimits := do
  let noRiskLimitTypes ← readGroup [49, 53, 50, 57] [49, 53, 51, 48] NoRiskLimitTypes.members NoRiskLimitTypes.decode tokens
  pure { noRiskLimitTypes }

theorem NoRiskLimits.decode_agrees (record : NoRiskLimits) (tokens : List Token)
    (agrees : ∀ tags ∈ NoRiskLimits.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoRiskLimits.decode tokens = some record := by
  have distinct : NoRiskLimits.tags.flatten.Nodup := by decide +kernel
  have noRiskLimitTypes := readGroup_partLed [49, 53, 50, 57] [49, 53, 51, 48] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within NoRiskLimitTypes.decode NoRiskLimitTypes.decode_encode NoRiskLimitTypes.led record.noRiskLimitTypes tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  simp only [NoRiskLimits.decode, noRiskLimitTypes, some_bind] <;> rfl

theorem NoRiskLimits.taken (record : NoRiskLimits) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within (by decide) (by decide) NoRiskLimitTypes.taken record.noRiskLimitTypes)
   (paired_none pairing)

def NoRiskLimits.members : List (List UInt8) := NoRiskLimits.tags.flatten

def NoRiskLimits.encode (entry : NoRiskLimits) : List Token := encodeParts entry.parts

theorem NoRiskLimits.decode_encode (entry : NoRiskLimits) : NoRiskLimits.decode entry.encode = some entry :=
  NoRiskLimits.decode_agrees entry _ (fun _ _ => rfl)

theorem NoRiskLimits.within (entry : NoRiskLimits) : ∀ token ∈ entry.encode, token.tag ∈ NoRiskLimits.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoRiskLimits.shape] at this

theorem NoRiskLimits.led (entry : NoRiskLimits) : Lead [49, 53, 50, 57] entry.encode :=
  lead_groupLed [49, 53, 50, 57] NoRiskLimitTypes.members NoRiskLimitTypes.encode NoRiskLimitTypes.within entry.noRiskLimitTypes _ NoRiskLimits.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure NoPartyRiskLimits where
  noPartyDetails : List NoPartyDetails  -- tag 1671
  noRiskLimits : List NoRiskLimits  -- tag 1669

def NoPartyRiskLimits.parts (record : NoPartyRiskLimits) : List Part :=
  [Part.groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within record.noPartyDetails,
   Part.group [49, 54, 54, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within record.noRiskLimits]

def NoPartyRiskLimits.tags : List (List (List UInt8)) :=
  [[49, 54, 55, 49] :: NoPartyDetails.members, [49, 54, 54, 57] :: NoRiskLimits.members]

theorem NoPartyRiskLimits.shape (record : NoPartyRiskLimits) : record.parts.map Part.tags = NoPartyRiskLimits.tags := rfl

def NoPartyRiskLimits.decode (tokens : List Token) : Option NoPartyRiskLimits := do
  let noPartyDetails ← readGroup [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.decode tokens
  let noRiskLimits ← readGroup [49, 54, 54, 57] [49, 53, 50, 57] NoRiskLimits.members NoRiskLimits.decode tokens
  pure { noPartyDetails, noRiskLimits }

theorem NoPartyRiskLimits.decode_agrees (record : NoPartyRiskLimits) (tokens : List Token)
    (agrees : ∀ tags ∈ NoPartyRiskLimits.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoPartyRiskLimits.decode tokens = some record := by
  have distinct : NoPartyRiskLimits.tags.flatten.Nodup := by decide +kernel
  have noPartyDetails := readGroup_partLed [49, 54, 55, 49] [49, 54, 57, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within NoPartyDetails.decode NoPartyDetails.decode_encode NoPartyDetails.led record.noPartyDetails tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have noRiskLimits := readGroup_part [49, 54, 54, 57] [49, 53, 50, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within NoRiskLimits.decode NoRiskLimits.decode_encode NoRiskLimits.led record.noRiskLimits tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  simp only [NoPartyRiskLimits.decode, noPartyDetails, noRiskLimits, some_bind] <;> rfl

theorem NoPartyRiskLimits.taken (record : NoPartyRiskLimits) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_groupLed pairing [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within (by decide) (by decide) NoPartyDetails.taken record.noPartyDetails)
   (paired_cons pairing _ _ (paired_group pairing [49, 54, 54, 57] NoRiskLimits.members NoRiskLimits.encode NoRiskLimits.within (by decide) (by decide) NoRiskLimits.taken record.noRiskLimits)
    (paired_none pairing))

def NoPartyRiskLimits.members : List (List UInt8) := NoPartyRiskLimits.tags.flatten

def NoPartyRiskLimits.encode (entry : NoPartyRiskLimits) : List Token := encodeParts entry.parts

theorem NoPartyRiskLimits.decode_encode (entry : NoPartyRiskLimits) : NoPartyRiskLimits.decode entry.encode = some entry :=
  NoPartyRiskLimits.decode_agrees entry _ (fun _ _ => rfl)

theorem NoPartyRiskLimits.within (entry : NoPartyRiskLimits) : ∀ token ∈ entry.encode, token.tag ∈ NoPartyRiskLimits.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoPartyRiskLimits.shape] at this

theorem NoPartyRiskLimits.led (entry : NoPartyRiskLimits) : Lead [49, 54, 55, 49] entry.encode :=
  lead_groupLed [49, 54, 55, 49] NoPartyDetails.members NoPartyDetails.encode NoPartyDetails.within entry.noPartyDetails _ NoPartyRiskLimits.tags.tail rfl (by decide +kernel) (by decide +kernel)

structure UserPartyRiskLimitsReport where
  noPartyRiskLimits : List NoPartyRiskLimits  -- tag 1677
  marketSegmentID : Terminated 1  -- tag 1300
  riskLimitRequestID : Terminated 1  -- tag 1666
  riskLimitReportID : Terminated 1  -- tag 1667

def UserPartyRiskLimitsReport.parts (record : UserPartyRiskLimitsReport) : List Part :=
  [Part.group [49, 54, 55, 55] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within record.noPartyRiskLimits,
   Part.required [49, 51, 48, 48] record.marketSegmentID,
   Part.required [49, 54, 54, 54] record.riskLimitRequestID,
   Part.required [49, 54, 54, 55] record.riskLimitReportID]

def UserPartyRiskLimitsReport.tags : List (List (List UInt8)) :=
  [[49, 54, 55, 55] :: NoPartyRiskLimits.members, [[49, 51, 48, 48]], [[49, 54, 54, 54]], [[49, 54, 54, 55]]]

theorem UserPartyRiskLimitsReport.shape (record : UserPartyRiskLimitsReport) : record.parts.map Part.tags = UserPartyRiskLimitsReport.tags := rfl

def UserPartyRiskLimitsReport.decode (tokens : List Token) : Option UserPartyRiskLimitsReport := do
  let noPartyRiskLimits ← readGroup [49, 54, 55, 55] [49, 54, 55, 49] NoPartyRiskLimits.members NoPartyRiskLimits.decode tokens
  let marketSegmentID ← readRequired [49, 51, 48, 48] tokens
  let riskLimitRequestID ← readRequired [49, 54, 54, 54] tokens
  let riskLimitReportID ← readRequired [49, 54, 54, 55] tokens
  pure { noPartyRiskLimits, marketSegmentID, riskLimitRequestID, riskLimitReportID }

theorem UserPartyRiskLimitsReport.decode_agrees (record : UserPartyRiskLimitsReport) (tokens : List Token)
    (agrees : ∀ tags ∈ UserPartyRiskLimitsReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserPartyRiskLimitsReport.decode tokens = some record := by
  have distinct : UserPartyRiskLimitsReport.tags.flatten.Nodup := by decide +kernel
  have noPartyRiskLimits := readGroup_part [49, 54, 55, 55] [49, 54, 55, 49] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within NoPartyRiskLimits.decode NoPartyRiskLimits.decode_encode NoPartyRiskLimits.led record.noPartyRiskLimits tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have marketSegmentID := readRequired_part [49, 51, 48, 48] record.marketSegmentID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have riskLimitRequestID := readRequired_part [49, 54, 54, 54] record.riskLimitRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have riskLimitReportID := readRequired_part [49, 54, 54, 55] record.riskLimitReportID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [UserPartyRiskLimitsReport.decode, noPartyRiskLimits, marketSegmentID, riskLimitRequestID, riskLimitReportID, some_bind] <;> rfl

theorem UserPartyRiskLimitsReport.taken (record : UserPartyRiskLimitsReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [49, 54, 55, 55] NoPartyRiskLimits.members NoPartyRiskLimits.encode NoPartyRiskLimits.within (by decide) (by decide) NoPartyRiskLimits.taken record.noPartyRiskLimits)
   (paired_cons pairing _ _ (paired_required pairing [49, 51, 48, 48] record.marketSegmentID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [49, 54, 54, 54] record.riskLimitRequestID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [49, 54, 54, 55] record.riskLimitReportID (by decide) (by decide))
      (paired_none pairing))))

structure UserPartyRiskLimitsUpdateReport where
  noPartyIDs : List NoPartyIDs  -- tag 453
  tradeDate : Terminated 1  -- tag 75
  listUpdateAction : Option (Terminated 1)  -- tag 1324
  riskLimitAction : Option (Terminated 1)  -- tag 1767
  uTransactTime : Terminated 1  -- tag 30060
  marketID : Terminated 1  -- tag 1301

def UserPartyRiskLimitsUpdateReport.parts (record : UserPartyRiskLimitsUpdateReport) : List Part :=
  [Part.group [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within record.noPartyIDs,
   Part.required [55, 53] record.tradeDate,
   Part.optional [49, 51, 50, 52] record.listUpdateAction,
   Part.optional [49, 55, 54, 55] record.riskLimitAction,
   Part.required [51, 48, 48, 54, 48] record.uTransactTime,
   Part.required [49, 51, 48, 49] record.marketID]

def UserPartyRiskLimitsUpdateReport.tags : List (List (List UInt8)) :=
  [[52, 53, 51] :: NoPartyIDs.members, [[55, 53]], [[49, 51, 50, 52]], [[49, 55, 54, 55]], [[51, 48, 48, 54, 48]], [[49, 51, 48, 49]]]

theorem UserPartyRiskLimitsUpdateReport.shape (record : UserPartyRiskLimitsUpdateReport) : record.parts.map Part.tags = UserPartyRiskLimitsUpdateReport.tags := rfl

def UserPartyRiskLimitsUpdateReport.decode (tokens : List Token) : Option UserPartyRiskLimitsUpdateReport := do
  let noPartyIDs ← readGroup [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.decode tokens
  let tradeDate ← readRequired [55, 53] tokens
  let listUpdateAction ← readOptional [49, 51, 50, 52] tokens
  let riskLimitAction ← readOptional [49, 55, 54, 55] tokens
  let uTransactTime ← readRequired [51, 48, 48, 54, 48] tokens
  let marketID ← readRequired [49, 51, 48, 49] tokens
  pure { noPartyIDs, tradeDate, listUpdateAction, riskLimitAction, uTransactTime, marketID }

theorem UserPartyRiskLimitsUpdateReport.decode_agrees (record : UserPartyRiskLimitsUpdateReport) (tokens : List Token)
    (agrees : ∀ tags ∈ UserPartyRiskLimitsUpdateReport.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserPartyRiskLimitsUpdateReport.decode tokens = some record := by
  have distinct : UserPartyRiskLimitsUpdateReport.tags.flatten.Nodup := by decide +kernel
  have noPartyIDs := readGroup_part [52, 53, 51] [52, 52, 56] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within NoPartyIDs.decode NoPartyIDs.decode_encode NoPartyIDs.led record.noPartyIDs tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have tradeDate := readRequired_part [55, 53] record.tradeDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have listUpdateAction := readOptional_part [49, 51, 50, 52] record.listUpdateAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have riskLimitAction := readOptional_part [49, 55, 54, 55] record.riskLimitAction tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have uTransactTime := readRequired_part [51, 48, 48, 54, 48] record.uTransactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have marketID := readRequired_part [49, 51, 48, 49] record.marketID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [UserPartyRiskLimitsUpdateReport.decode, noPartyIDs, tradeDate, listUpdateAction, riskLimitAction, uTransactTime, marketID, some_bind] <;> rfl

theorem UserPartyRiskLimitsUpdateReport.taken (record : UserPartyRiskLimitsUpdateReport) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_group pairing [52, 53, 51] NoPartyIDs.members NoPartyIDs.encode NoPartyIDs.within (by decide) (by decide) NoPartyIDs.taken record.noPartyIDs)
   (paired_cons pairing _ _ (paired_required pairing [55, 53] record.tradeDate (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 51, 50, 52] record.listUpdateAction (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 55, 54, 55] record.riskLimitAction (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 48, 48, 54, 48] record.uTransactTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [49, 51, 48, 49] record.marketID (by decide) (by decide))
        (paired_none pairing))))))

structure UserResponse where
  username : Terminated 1  -- tag 553
  userRequestID : Terminated 1  -- tag 923
  userStatus : Terminated 1  -- tag 926

def UserResponse.parts (record : UserResponse) : List Part :=
  [Part.required [53, 53, 51] record.username,
   Part.required [57, 50, 51] record.userRequestID,
   Part.required [57, 50, 54] record.userStatus]

def UserResponse.tags : List (List (List UInt8)) :=
  [[[53, 53, 51]], [[57, 50, 51]], [[57, 50, 54]]]

theorem UserResponse.shape (record : UserResponse) : record.parts.map Part.tags = UserResponse.tags := rfl

def UserResponse.decode (tokens : List Token) : Option UserResponse := do
  let username ← readRequired [53, 53, 51] tokens
  let userRequestID ← readRequired [57, 50, 51] tokens
  let userStatus ← readRequired [57, 50, 54] tokens
  pure { username, userRequestID, userStatus }

theorem UserResponse.decode_agrees (record : UserResponse) (tokens : List Token)
    (agrees : ∀ tags ∈ UserResponse.tags, select tags tokens = select tags (encodeParts record.parts)) :
    UserResponse.decode tokens = some record := by
  have distinct : UserResponse.tags.flatten.Nodup := by decide +kernel
  have username := readRequired_part [53, 53, 51] record.username tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have userRequestID := readRequired_part [57, 50, 51] record.userRequestID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have userStatus := readRequired_part [57, 50, 54] record.userStatus tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  simp only [UserResponse.decode, username, userRequestID, userStatus, some_bind] <;> rfl

theorem UserResponse.taken (record : UserResponse) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 53, 51] record.username (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [57, 50, 51] record.userRequestID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [57, 50, 54] record.userStatus (by decide) (by decide))
     (paired_none pairing)))

inductive Message where
  | businessMessageAck (header : Header) (r0 : BusinessMessageAck)
  | businessMessageReject (header : Header) (r0 : BusinessMessageReject)
  | executionReport (header : Header) (r0 : ExecutionReport)
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | quote (header : Header) (r0 : Quote)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | securityStatus (header : Header) (r0 : SecurityStatus)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | sessionDetailsList (header : Header) (r0 : SessionDetailsList)
  | testRequest (header : Header) (r0 : TestRequest)
  | tradeCaptureReport (header : Header) (r0 : TradeCaptureReport)
  | tradingSessionStatus (header : Header) (r0 : TradingSessionStatus)
  | userNotification (header : Header) (r0 : UserNotification)
  | userOrderMassActionReport (header : Header) (r0 : UserOrderMassActionReport)
  | userPartyActionReport (header : Header) (r0 : UserPartyActionReport)
  | userPartyEntitlementsUpdateReport (header : Header) (r0 : UserPartyEntitlementsUpdateReport)
  | userPartyRiskLimitsReport (header : Header) (r0 : UserPartyRiskLimitsReport)
  | userPartyRiskLimitsUpdateReport (header : Header) (r0 : UserPartyRiskLimitsUpdateReport)
  | userResponse (header : Header) (r0 : UserResponse)

def Message.tokens : Message → List Token
  | .businessMessageAck header r0 => ⟨[51, 53], [85, 50, 56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .businessMessageReject header r0 => ⟨[51, 53], [106]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .executionReport header r0 => ⟨[51, 53], [56]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .quote header r0 => ⟨[51, 53], [83]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .securityStatus header r0 => ⟨[51, 53], [102]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sessionDetailsList header r0 => ⟨[51, 53], [85, 54]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradeCaptureReport header r0 => ⟨[51, 53], [65, 69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .tradingSessionStatus header r0 => ⟨[51, 53], [104]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userNotification header r0 => ⟨[51, 53], [85, 67, 66]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userOrderMassActionReport header r0 => ⟨[51, 53], [85, 66, 90]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userPartyActionReport header r0 => ⟨[51, 53], [85, 68, 73]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userPartyEntitlementsUpdateReport header r0 => ⟨[51, 53], [85, 67, 90]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userPartyRiskLimitsReport header r0 => ⟨[51, 53], [85, 67, 77]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userPartyRiskLimitsUpdateReport header r0 => ⟨[51, 53], [85, 67, 82]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .userResponse header r0 => ⟨[51, 53], [66, 70]⟩ :: encodeParts (header.parts ++ r0.parts)

def Message.decode : List Token → Option Message
  | [] => none
  | token :: rest =>
    if token.tag = [51, 53] then
      if token.value = [85, 50, 56] then
        if known (Header.tags ++ BusinessMessageAck.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageAck.decode rest
          pure (.businessMessageAck header r0)
        else none
      else if token.value = [106] then
        if known (Header.tags ++ BusinessMessageReject.tags) rest then do
          let header ← Header.decode rest
          let r0 ← BusinessMessageReject.decode rest
          pure (.businessMessageReject header r0)
        else none
      else if token.value = [56] then
        if known (Header.tags ++ ExecutionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← ExecutionReport.decode rest
          pure (.executionReport header r0)
        else none
      else if token.value = [48] then
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
      else if token.value = [83] then
        if known (Header.tags ++ Quote.tags) rest then do
          let header ← Header.decode rest
          let r0 ← Quote.decode rest
          pure (.quote header r0)
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
      else if token.value = [102] then
        if known (Header.tags ++ SecurityStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SecurityStatus.decode rest
          pure (.securityStatus header r0)
        else none
      else if token.value = [52] then
        if known (Header.tags ++ SequenceReset.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SequenceReset.decode rest
          pure (.sequenceReset header r0)
        else none
      else if token.value = [85, 54] then
        if known (Header.tags ++ SessionDetailsList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← SessionDetailsList.decode rest
          pure (.sessionDetailsList header r0)
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
      else if token.value = [104] then
        if known (Header.tags ++ TradingSessionStatus.tags) rest then do
          let header ← Header.decode rest
          let r0 ← TradingSessionStatus.decode rest
          pure (.tradingSessionStatus header r0)
        else none
      else if token.value = [85, 67, 66] then
        if known (Header.tags ++ UserNotification.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserNotification.decode rest
          pure (.userNotification header r0)
        else none
      else if token.value = [85, 66, 90] then
        if known (Header.tags ++ UserOrderMassActionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserOrderMassActionReport.decode rest
          pure (.userOrderMassActionReport header r0)
        else none
      else if token.value = [85, 68, 73] then
        if known (Header.tags ++ UserPartyActionReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserPartyActionReport.decode rest
          pure (.userPartyActionReport header r0)
        else none
      else if token.value = [85, 67, 90] then
        if known (Header.tags ++ UserPartyEntitlementsUpdateReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserPartyEntitlementsUpdateReport.decode rest
          pure (.userPartyEntitlementsUpdateReport header r0)
        else none
      else if token.value = [85, 67, 77] then
        if known (Header.tags ++ UserPartyRiskLimitsReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserPartyRiskLimitsReport.decode rest
          pure (.userPartyRiskLimitsReport header r0)
        else none
      else if token.value = [85, 67, 82] then
        if known (Header.tags ++ UserPartyRiskLimitsUpdateReport.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserPartyRiskLimitsUpdateReport.decode rest
          pure (.userPartyRiskLimitsUpdateReport header r0)
        else none
      else if token.value = [66, 70] then
        if known (Header.tags ++ UserResponse.tags) rest then do
          let header ← Header.decode rest
          let r0 ← UserResponse.decode rest
          pure (.userResponse header r0)
        else none
      else none
    else none

theorem Message.decode_businessMessageAck (header : Header) (r0 : BusinessMessageAck) :
    Message.decode (Message.tokens (.businessMessageAck header r0)) = some (.businessMessageAck header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageAck.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageAck.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageAck.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageAck.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, some_bind] <;> rfl

theorem Message.decode_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decode (Message.tokens (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) rfl rfl (by decide +kernel))
  have c1 := BusinessMessageReject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (BusinessMessageReject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ BusinessMessageReject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decode (Message.tokens (.executionReport header r0)) = some (.executionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) rfl rfl (by decide +kernel))
  have c1 := ExecutionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ExecutionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ExecutionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
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

theorem Message.decode_quote (header : Header) (r0 : Quote) :
    Message.decode (Message.tokens (.quote header r0)) = some (.quote header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) rfl rfl (by decide +kernel))
  have c1 := Quote.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Quote.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Quote.tags) rfl
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

theorem Message.decode_securityStatus (header : Header) (r0 : SecurityStatus) :
    Message.decode (Message.tokens (.securityStatus header r0)) = some (.securityStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatus.tags) rfl rfl (by decide +kernel))
  have c1 := SecurityStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SecurityStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SecurityStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_sessionDetailsList (header : Header) (r0 : SessionDetailsList) :
    Message.decode (Message.tokens (.sessionDetailsList header r0)) = some (.sessionDetailsList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SessionDetailsList.tags) rfl rfl (by decide +kernel))
  have c1 := SessionDetailsList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SessionDetailsList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SessionDetailsList.tags) rfl
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

theorem Message.decode_tradingSessionStatus (header : Header) (r0 : TradingSessionStatus) :
    Message.decode (Message.tokens (.tradingSessionStatus header r0)) = some (.tradingSessionStatus header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatus.tags) rfl rfl (by decide +kernel))
  have c1 := TradingSessionStatus.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TradingSessionStatus.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TradingSessionStatus.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userNotification (header : Header) (r0 : UserNotification) :
    Message.decode (Message.tokens (.userNotification header r0)) = some (.userNotification header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) rfl rfl (by decide +kernel))
  have c1 := UserNotification.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserNotification.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserNotification.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userOrderMassActionReport (header : Header) (r0 : UserOrderMassActionReport) :
    Message.decode (Message.tokens (.userOrderMassActionReport header r0)) = some (.userOrderMassActionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserOrderMassActionReport.tags) rfl rfl (by decide +kernel))
  have c1 := UserOrderMassActionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserOrderMassActionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserOrderMassActionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userPartyActionReport (header : Header) (r0 : UserPartyActionReport) :
    Message.decode (Message.tokens (.userPartyActionReport header r0)) = some (.userPartyActionReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyActionReport.tags) rfl rfl (by decide +kernel))
  have c1 := UserPartyActionReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyActionReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserPartyActionReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userPartyEntitlementsUpdateReport (header : Header) (r0 : UserPartyEntitlementsUpdateReport) :
    Message.decode (Message.tokens (.userPartyEntitlementsUpdateReport header r0)) = some (.userPartyEntitlementsUpdateReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyEntitlementsUpdateReport.tags) rfl rfl (by decide +kernel))
  have c1 := UserPartyEntitlementsUpdateReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyEntitlementsUpdateReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserPartyEntitlementsUpdateReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userPartyRiskLimitsReport (header : Header) (r0 : UserPartyRiskLimitsReport) :
    Message.decode (Message.tokens (.userPartyRiskLimitsReport header r0)) = some (.userPartyRiskLimitsReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsReport.tags) rfl rfl (by decide +kernel))
  have c1 := UserPartyRiskLimitsReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserPartyRiskLimitsReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userPartyRiskLimitsUpdateReport (header : Header) (r0 : UserPartyRiskLimitsUpdateReport) :
    Message.decode (Message.tokens (.userPartyRiskLimitsUpdateReport header r0)) = some (.userPartyRiskLimitsUpdateReport header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsUpdateReport.tags) rfl rfl (by decide +kernel))
  have c1 := UserPartyRiskLimitsUpdateReport.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserPartyRiskLimitsUpdateReport.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserPartyRiskLimitsUpdateReport.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_userResponse (header : Header) (r0 : UserResponse) :
    Message.decode (Message.tokens (.userResponse header r0)) = some (.userResponse header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) rfl rfl (by decide +kernel))
  have c1 := UserResponse.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (UserResponse.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ UserResponse.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | businessMessageAck header r0 => exact Message.decode_businessMessageAck header r0
  | businessMessageReject header r0 => exact Message.decode_businessMessageReject header r0
  | executionReport header r0 => exact Message.decode_executionReport header r0
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | quote header r0 => exact Message.decode_quote header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | securityStatus header r0 => exact Message.decode_securityStatus header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | sessionDetailsList header r0 => exact Message.decode_sessionDetailsList header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0
  | tradeCaptureReport header r0 => exact Message.decode_tradeCaptureReport header r0
  | tradingSessionStatus header r0 => exact Message.decode_tradingSessionStatus header r0
  | userNotification header r0 => exact Message.decode_userNotification header r0
  | userOrderMassActionReport header r0 => exact Message.decode_userOrderMassActionReport header r0
  | userPartyActionReport header r0 => exact Message.decode_userPartyActionReport header r0
  | userPartyEntitlementsUpdateReport header r0 => exact Message.decode_userPartyEntitlementsUpdateReport header r0
  | userPartyRiskLimitsReport header r0 => exact Message.decode_userPartyRiskLimitsReport header r0
  | userPartyRiskLimitsUpdateReport header r0 => exact Message.decode_userPartyRiskLimitsUpdateReport header r0
  | userResponse header r0 => exact Message.decode_userResponse header r0

def Message.encode (message : Message) : List UInt8 := encodeTokens message.tokens

def Message.decodeBytes (bytes : List UInt8) : Option Message := do
  let tokens ← decodeTokens pairing bytes.length bytes
  Message.decode tokens

theorem Message.decodeBytes_businessMessageAck (header : Header) (r0 : BusinessMessageAck) :
    Message.decodeBytes (Message.encode (.businessMessageAck header r0)) = some (.businessMessageAck header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 50, 56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageAck.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageAck header r0

theorem Message.decodeBytes_businessMessageReject (header : Header) (r0 : BusinessMessageReject) :
    Message.decodeBytes (Message.encode (.businessMessageReject header r0)) = some (.businessMessageReject header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [106]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (BusinessMessageReject.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_businessMessageReject header r0

theorem Message.decodeBytes_executionReport (header : Header) (r0 : ExecutionReport) :
    Message.decodeBytes (Message.encode (.executionReport header r0)) = some (.executionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [56]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (ExecutionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_executionReport header r0

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

theorem Message.decodeBytes_quote (header : Header) (r0 : Quote) :
    Message.decodeBytes (Message.encode (.quote header r0)) = some (.quote header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [83]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (Quote.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_quote header r0

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

theorem Message.decodeBytes_securityStatus (header : Header) (r0 : SecurityStatus) :
    Message.decodeBytes (Message.encode (.securityStatus header r0)) = some (.securityStatus header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [102]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SecurityStatus.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_securityStatus header r0

theorem Message.decodeBytes_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decodeBytes (Message.encode (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [52]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SequenceReset.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sequenceReset header r0

theorem Message.decodeBytes_sessionDetailsList (header : Header) (r0 : SessionDetailsList) :
    Message.decodeBytes (Message.encode (.sessionDetailsList header r0)) = some (.sessionDetailsList header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 54]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (SessionDetailsList.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_sessionDetailsList header r0

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

theorem Message.decodeBytes_tradingSessionStatus (header : Header) (r0 : TradingSessionStatus) :
    Message.decodeBytes (Message.encode (.tradingSessionStatus header r0)) = some (.tradingSessionStatus header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [104]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (TradingSessionStatus.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_tradingSessionStatus header r0

theorem Message.decodeBytes_userNotification (header : Header) (r0 : UserNotification) :
    Message.decodeBytes (Message.encode (.userNotification header r0)) = some (.userNotification header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 66]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserNotification.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userNotification header r0

theorem Message.decodeBytes_userOrderMassActionReport (header : Header) (r0 : UserOrderMassActionReport) :
    Message.decodeBytes (Message.encode (.userOrderMassActionReport header r0)) = some (.userOrderMassActionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 66, 90]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserOrderMassActionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userOrderMassActionReport header r0

theorem Message.decodeBytes_userPartyActionReport (header : Header) (r0 : UserPartyActionReport) :
    Message.decodeBytes (Message.encode (.userPartyActionReport header r0)) = some (.userPartyActionReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 68, 73]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserPartyActionReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userPartyActionReport header r0

theorem Message.decodeBytes_userPartyEntitlementsUpdateReport (header : Header) (r0 : UserPartyEntitlementsUpdateReport) :
    Message.decodeBytes (Message.encode (.userPartyEntitlementsUpdateReport header r0)) = some (.userPartyEntitlementsUpdateReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 90]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserPartyEntitlementsUpdateReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userPartyEntitlementsUpdateReport header r0

theorem Message.decodeBytes_userPartyRiskLimitsReport (header : Header) (r0 : UserPartyRiskLimitsReport) :
    Message.decodeBytes (Message.encode (.userPartyRiskLimitsReport header r0)) = some (.userPartyRiskLimitsReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 77]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserPartyRiskLimitsReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userPartyRiskLimitsReport header r0

theorem Message.decodeBytes_userPartyRiskLimitsUpdateReport (header : Header) (r0 : UserPartyRiskLimitsUpdateReport) :
    Message.decodeBytes (Message.encode (.userPartyRiskLimitsUpdateReport header r0)) = some (.userPartyRiskLimitsUpdateReport header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [85, 67, 82]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserPartyRiskLimitsUpdateReport.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userPartyRiskLimitsUpdateReport header r0

theorem Message.decodeBytes_userResponse (header : Header) (r0 : UserResponse) :
    Message.decodeBytes (Message.encode (.userResponse header r0)) = some (.userResponse header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [66, 70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (UserResponse.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_userResponse header r0

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | businessMessageAck header r0 => exact Message.decodeBytes_businessMessageAck header r0
  | businessMessageReject header r0 => exact Message.decodeBytes_businessMessageReject header r0
  | executionReport header r0 => exact Message.decodeBytes_executionReport header r0
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | quote header r0 => exact Message.decodeBytes_quote header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | securityStatus header r0 => exact Message.decodeBytes_securityStatus header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | sessionDetailsList header r0 => exact Message.decodeBytes_sessionDetailsList header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0
  | tradeCaptureReport header r0 => exact Message.decodeBytes_tradeCaptureReport header r0
  | tradingSessionStatus header r0 => exact Message.decodeBytes_tradingSessionStatus header r0
  | userNotification header r0 => exact Message.decodeBytes_userNotification header r0
  | userOrderMassActionReport header r0 => exact Message.decodeBytes_userOrderMassActionReport header r0
  | userPartyActionReport header r0 => exact Message.decodeBytes_userPartyActionReport header r0
  | userPartyEntitlementsUpdateReport header r0 => exact Message.decodeBytes_userPartyEntitlementsUpdateReport header r0
  | userPartyRiskLimitsReport header r0 => exact Message.decodeBytes_userPartyRiskLimitsReport header r0
  | userPartyRiskLimitsUpdateReport header r0 => exact Message.decodeBytes_userPartyRiskLimitsUpdateReport header r0
  | userResponse header r0 => exact Message.decodeBytes_userResponse header r0

/-- BeginString as the venue fixes it: FIX.4.4 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 52, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.EurexT7CashorderentryFixV141Exchange
