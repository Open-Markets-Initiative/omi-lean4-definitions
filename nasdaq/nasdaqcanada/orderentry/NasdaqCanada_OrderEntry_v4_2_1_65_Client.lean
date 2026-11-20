import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq)  v4.2.1, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNasdaqcanadaOrderentryFixV42165Client

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  possDupFlag : Option (Terminated 1)  -- tag 43
  senderCompID : Terminated 1  -- tag 49
  senderSubID : Option (Terminated 1)  -- tag 50
  sendingTime : Terminated 1  -- tag 52
  targetCompID : Terminated 1  -- tag 56
  targetSubID : Option (Terminated 1)  -- tag 57
  possResend : Option (Terminated 1)  -- tag 97

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.optional [52, 51] record.possDupFlag,
   Part.required [52, 57] record.senderCompID,
   Part.optional [53, 48] record.senderSubID,
   Part.required [53, 50] record.sendingTime,
   Part.required [53, 54] record.targetCompID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [57, 55] record.possResend]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 51]], [[52, 57]], [[53, 48]], [[53, 50]], [[53, 54]], [[53, 55]], [[57, 55]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possResend ← readOptional [57, 55] tokens
  pure { msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend }

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
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, possDupFlag, senderCompID, senderSubID, sendingTime, targetCompID, targetSubID, possResend, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_none pairing))))))))

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

structure MarketParticipantCommand where
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  exDestination : Option (Terminated 1)  -- tag 100
  uMIRUserID : Terminated 1  -- tag 6751
  partCommandID : Terminated 1  -- tag 6789
  gEFCommitVolume : Terminated 1  -- tag 6799

def MarketParticipantCommand.parts (record : MarketParticipantCommand) : List Part :=
  [Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [49, 48, 48] record.exDestination,
   Part.required [54, 55, 53, 49] record.uMIRUserID,
   Part.required [54, 55, 56, 57] record.partCommandID,
   Part.required [54, 55, 57, 57] record.gEFCommitVolume]

def MarketParticipantCommand.tags : List (List (List UInt8)) :=
  [[[53, 52]], [[53, 53]], [[49, 48, 48]], [[54, 55, 53, 49]], [[54, 55, 56, 57]], [[54, 55, 57, 57]]]

theorem MarketParticipantCommand.shape (record : MarketParticipantCommand) : record.parts.map Part.tags = MarketParticipantCommand.tags := rfl

def MarketParticipantCommand.decode (tokens : List Token) : Option MarketParticipantCommand := do
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let uMIRUserID ← readRequired [54, 55, 53, 49] tokens
  let partCommandID ← readRequired [54, 55, 56, 57] tokens
  let gEFCommitVolume ← readRequired [54, 55, 57, 57] tokens
  pure { side, symbol, exDestination, uMIRUserID, partCommandID, gEFCommitVolume }

theorem MarketParticipantCommand.decode_agrees (record : MarketParticipantCommand) (tokens : List Token)
    (agrees : ∀ tags ∈ MarketParticipantCommand.tags, select tags tokens = select tags (encodeParts record.parts)) :
    MarketParticipantCommand.decode tokens = some record := by
  have distinct : MarketParticipantCommand.tags.flatten.Nodup := by decide +kernel
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have uMIRUserID := readRequired_part [54, 55, 53, 49] record.uMIRUserID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have partCommandID := readRequired_part [54, 55, 56, 57] record.partCommandID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have gEFCommitVolume := readRequired_part [54, 55, 57, 57] record.gEFCommitVolume tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [MarketParticipantCommand.decode, side, symbol, exDestination, uMIRUserID, partCommandID, gEFCommitVolume, some_bind] <;> rfl

theorem MarketParticipantCommand.taken (record : MarketParticipantCommand) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48] record.exDestination (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 55, 53, 49] record.uMIRUserID (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [54, 55, 56, 57] record.partCommandID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 55, 57, 57] record.gEFCommitVolume (by decide) (by decide))
        (paired_none pairing))))))

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  exDestination : Option (Terminated 1)  -- tag 100
  uMIRUserID : Terminated 1  -- tag 6751
  basketTrade : Option (Terminated 1)  -- tag 6754
  programTrade : Option (Terminated 1)  -- tag 6755
  anonymous : Option (Terminated 1)  -- tag 6761
  bypass : Option (Terminated 1)  -- tag 6791
  shortMarkingExempt : Option (Terminated 1)  -- tag 7729
  pOComment : Option (Terminated 1)  -- tag 7737

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 48, 48] record.exDestination,
   Part.required [54, 55, 53, 49] record.uMIRUserID,
   Part.optional [54, 55, 53, 52] record.basketTrade,
   Part.optional [54, 55, 53, 53] record.programTrade,
   Part.optional [54, 55, 54, 49] record.anonymous,
   Part.optional [54, 55, 57, 49] record.bypass,
   Part.optional [55, 55, 50, 57] record.shortMarkingExempt,
   Part.optional [55, 55, 51, 55] record.pOComment]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 48, 48]], [[54, 55, 53, 49]], [[54, 55, 53, 52]], [[54, 55, 53, 53]], [[54, 55, 54, 49]], [[54, 55, 57, 49]], [[55, 55, 50, 57]], [[55, 55, 51, 55]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let exDestination ← readOptional [49, 48, 48] tokens
  let uMIRUserID ← readRequired [54, 55, 53, 49] tokens
  let basketTrade ← readOptional [54, 55, 53, 52] tokens
  let programTrade ← readOptional [54, 55, 53, 53] tokens
  let anonymous ← readOptional [54, 55, 54, 49] tokens
  let bypass ← readOptional [54, 55, 57, 49] tokens
  let shortMarkingExempt ← readOptional [55, 55, 50, 57] tokens
  let pOComment ← readOptional [55, 55, 51, 55] tokens
  pure { clOrdID, execInst, handlInst, orderQty, ordType, price, symbol, timeInForce, transactTime, exDestination, uMIRUserID, basketTrade, programTrade, anonymous, bypass, shortMarkingExempt, pOComment }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have exDestination := readOptional_part [49, 48, 48] record.exDestination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have uMIRUserID := readRequired_part [54, 55, 53, 49] record.uMIRUserID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have basketTrade := readOptional_part [54, 55, 53, 52] record.basketTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have programTrade := readOptional_part [54, 55, 53, 53] record.programTrade tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have anonymous := readOptional_part [54, 55, 54, 49] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have bypass := readOptional_part [54, 55, 57, 49] record.bypass tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have shortMarkingExempt := readOptional_part [55, 55, 50, 57] record.shortMarkingExempt tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have pOComment := readOptional_part [55, 55, 51, 55] record.pOComment tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, execInst, handlInst, orderQty, ordType, price, symbol, timeInForce, transactTime, exDestination, uMIRUserID, basketTrade, programTrade, anonymous, bypass, shortMarkingExempt, pOComment, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 48] record.exDestination (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [54, 55, 53, 49] record.uMIRUserID (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 52] record.basketTrade (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 53] record.programTrade (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 49] record.anonymous (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 49] record.bypass (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [55, 55, 50, 57] record.shortMarkingExempt (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 55] record.pOComment (by decide) (by decide))
                   (paired_none pairing)))))))))))))))))

structure NewOrderSingleCross where
  settlType : Option (Terminated 1)  -- tag 63
  settlDate : Option (Terminated 1)  -- tag 64
  cHIXBuyAccountType : Terminated 1  -- tag 6767
  cHIXSellAccountType : Terminated 1  -- tag 6768
  cHIXBuyAccountID : Option (Terminated 1)  -- tag 6769
  cHIXSellAccountID : Option (Terminated 1)  -- tag 6770
  cHIXBuyRegulationID : Option (Terminated 1)  -- tag 6771
  cHIXSellRegulationID : Option (Terminated 1)  -- tag 6772
  crossType : Option (Terminated 1)  -- tag 6773
  cHIXBuyJitney : Option (Terminated 1)  -- tag 6781
  cHIXSellJitney : Option (Terminated 1)  -- tag 6782
  facilitationQty : Option (Terminated 1)  -- tag 20050
  facilitationSide : Option (Terminated 1)  -- tag 20051
  buyCustomerAccount : Option (Terminated 1)  -- tag 20201
  sellCustomerAccount : Option (Terminated 1)  -- tag 20202
  buyAlgorithmID : Option (Terminated 1)  -- tag 20203
  sellAlgorithmID : Option (Terminated 1)  -- tag 20204
  buyCustomerLEI : Option (Terminated 1)  -- tag 20205
  sellCustomerLEI : Option (Terminated 1)  -- tag 20206
  buyBrokerLEI : Option (Terminated 1)  -- tag 20207
  sellBrokerLEI : Option (Terminated 1)  -- tag 20208
  buyOrderOrigination : Option (Terminated 1)  -- tag 20209
  sellOrderOrigination : Option (Terminated 1)  -- tag 20210
  buyRoutingArrangementIndicator : Option (Terminated 1)  -- tag 20211
  sellRoutingArrangementIndicator : Option (Terminated 1)  -- tag 20212

def NewOrderSingleCross.parts (record : NewOrderSingleCross) : List Part :=
  [Part.optional [54, 51] record.settlType,
   Part.optional [54, 52] record.settlDate,
   Part.required [54, 55, 54, 55] record.cHIXBuyAccountType,
   Part.required [54, 55, 54, 56] record.cHIXSellAccountType,
   Part.optional [54, 55, 54, 57] record.cHIXBuyAccountID,
   Part.optional [54, 55, 55, 48] record.cHIXSellAccountID,
   Part.optional [54, 55, 55, 49] record.cHIXBuyRegulationID,
   Part.optional [54, 55, 55, 50] record.cHIXSellRegulationID,
   Part.optional [54, 55, 55, 51] record.crossType,
   Part.optional [54, 55, 56, 49] record.cHIXBuyJitney,
   Part.optional [54, 55, 56, 50] record.cHIXSellJitney,
   Part.optional [50, 48, 48, 53, 48] record.facilitationQty,
   Part.optional [50, 48, 48, 53, 49] record.facilitationSide,
   Part.optional [50, 48, 50, 48, 49] record.buyCustomerAccount,
   Part.optional [50, 48, 50, 48, 50] record.sellCustomerAccount,
   Part.optional [50, 48, 50, 48, 51] record.buyAlgorithmID,
   Part.optional [50, 48, 50, 48, 52] record.sellAlgorithmID,
   Part.optional [50, 48, 50, 48, 53] record.buyCustomerLEI,
   Part.optional [50, 48, 50, 48, 54] record.sellCustomerLEI,
   Part.optional [50, 48, 50, 48, 55] record.buyBrokerLEI,
   Part.optional [50, 48, 50, 48, 56] record.sellBrokerLEI,
   Part.optional [50, 48, 50, 48, 57] record.buyOrderOrigination,
   Part.optional [50, 48, 50, 49, 48] record.sellOrderOrigination,
   Part.optional [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator,
   Part.optional [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator]

def NewOrderSingleCross.tags : List (List (List UInt8)) :=
  [[[54, 51]], [[54, 52]], [[54, 55, 54, 55]], [[54, 55, 54, 56]], [[54, 55, 54, 57]], [[54, 55, 55, 48]], [[54, 55, 55, 49]], [[54, 55, 55, 50]], [[54, 55, 55, 51]], [[54, 55, 56, 49]], [[54, 55, 56, 50]], [[50, 48, 48, 53, 48]], [[50, 48, 48, 53, 49]], [[50, 48, 50, 48, 49]], [[50, 48, 50, 48, 50]], [[50, 48, 50, 48, 51]], [[50, 48, 50, 48, 52]], [[50, 48, 50, 48, 53]], [[50, 48, 50, 48, 54]], [[50, 48, 50, 48, 55]], [[50, 48, 50, 48, 56]], [[50, 48, 50, 48, 57]], [[50, 48, 50, 49, 48]], [[50, 48, 50, 49, 49]], [[50, 48, 50, 49, 50]]]

theorem NewOrderSingleCross.shape (record : NewOrderSingleCross) : record.parts.map Part.tags = NewOrderSingleCross.tags := rfl

def NewOrderSingleCross.decode (tokens : List Token) : Option NewOrderSingleCross := do
  let settlType ← readOptional [54, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let cHIXBuyAccountType ← readRequired [54, 55, 54, 55] tokens
  let cHIXSellAccountType ← readRequired [54, 55, 54, 56] tokens
  let cHIXBuyAccountID ← readOptional [54, 55, 54, 57] tokens
  let cHIXSellAccountID ← readOptional [54, 55, 55, 48] tokens
  let cHIXBuyRegulationID ← readOptional [54, 55, 55, 49] tokens
  let cHIXSellRegulationID ← readOptional [54, 55, 55, 50] tokens
  let crossType ← readOptional [54, 55, 55, 51] tokens
  let cHIXBuyJitney ← readOptional [54, 55, 56, 49] tokens
  let cHIXSellJitney ← readOptional [54, 55, 56, 50] tokens
  let facilitationQty ← readOptional [50, 48, 48, 53, 48] tokens
  let facilitationSide ← readOptional [50, 48, 48, 53, 49] tokens
  let buyCustomerAccount ← readOptional [50, 48, 50, 48, 49] tokens
  let sellCustomerAccount ← readOptional [50, 48, 50, 48, 50] tokens
  let buyAlgorithmID ← readOptional [50, 48, 50, 48, 51] tokens
  let sellAlgorithmID ← readOptional [50, 48, 50, 48, 52] tokens
  let buyCustomerLEI ← readOptional [50, 48, 50, 48, 53] tokens
  let sellCustomerLEI ← readOptional [50, 48, 50, 48, 54] tokens
  let buyBrokerLEI ← readOptional [50, 48, 50, 48, 55] tokens
  let sellBrokerLEI ← readOptional [50, 48, 50, 48, 56] tokens
  let buyOrderOrigination ← readOptional [50, 48, 50, 48, 57] tokens
  let sellOrderOrigination ← readOptional [50, 48, 50, 49, 48] tokens
  let buyRoutingArrangementIndicator ← readOptional [50, 48, 50, 49, 49] tokens
  let sellRoutingArrangementIndicator ← readOptional [50, 48, 50, 49, 50] tokens
  pure { settlType, settlDate, cHIXBuyAccountType, cHIXSellAccountType, cHIXBuyAccountID, cHIXSellAccountID, cHIXBuyRegulationID, cHIXSellRegulationID, crossType, cHIXBuyJitney, cHIXSellJitney, facilitationQty, facilitationSide, buyCustomerAccount, sellCustomerAccount, buyAlgorithmID, sellAlgorithmID, buyCustomerLEI, sellCustomerLEI, buyBrokerLEI, sellBrokerLEI, buyOrderOrigination, sellOrderOrigination, buyRoutingArrangementIndicator, sellRoutingArrangementIndicator }

theorem NewOrderSingleCross.decode_agrees (record : NewOrderSingleCross) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingleCross.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingleCross.decode tokens = some record := by
  have distinct : NewOrderSingleCross.tags.flatten.Nodup := by decide +kernel
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cHIXBuyAccountType := readRequired_part [54, 55, 54, 55] record.cHIXBuyAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cHIXSellAccountType := readRequired_part [54, 55, 54, 56] record.cHIXSellAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cHIXBuyAccountID := readOptional_part [54, 55, 54, 57] record.cHIXBuyAccountID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cHIXSellAccountID := readOptional_part [54, 55, 55, 48] record.cHIXSellAccountID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cHIXBuyRegulationID := readOptional_part [54, 55, 55, 49] record.cHIXBuyRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cHIXSellRegulationID := readOptional_part [54, 55, 55, 50] record.cHIXSellRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have crossType := readOptional_part [54, 55, 55, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cHIXBuyJitney := readOptional_part [54, 55, 56, 49] record.cHIXBuyJitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have cHIXSellJitney := readOptional_part [54, 55, 56, 50] record.cHIXSellJitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have facilitationQty := readOptional_part [50, 48, 48, 53, 48] record.facilitationQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have facilitationSide := readOptional_part [50, 48, 48, 53, 49] record.facilitationSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have buyCustomerAccount := readOptional_part [50, 48, 50, 48, 49] record.buyCustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have sellCustomerAccount := readOptional_part [50, 48, 50, 48, 50] record.sellCustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have buyAlgorithmID := readOptional_part [50, 48, 50, 48, 51] record.buyAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have sellAlgorithmID := readOptional_part [50, 48, 50, 48, 52] record.sellAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have buyCustomerLEI := readOptional_part [50, 48, 50, 48, 53] record.buyCustomerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have sellCustomerLEI := readOptional_part [50, 48, 50, 48, 54] record.sellCustomerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have buyBrokerLEI := readOptional_part [50, 48, 50, 48, 55] record.buyBrokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have sellBrokerLEI := readOptional_part [50, 48, 50, 48, 56] record.sellBrokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have buyOrderOrigination := readOptional_part [50, 48, 50, 48, 57] record.buyOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have sellOrderOrigination := readOptional_part [50, 48, 50, 49, 48] record.sellOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have buyRoutingArrangementIndicator := readOptional_part [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have sellRoutingArrangementIndicator := readOptional_part [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NewOrderSingleCross.decode, settlType, settlDate, cHIXBuyAccountType, cHIXSellAccountType, cHIXBuyAccountID, cHIXSellAccountID, cHIXBuyRegulationID, cHIXSellRegulationID, crossType, cHIXBuyJitney, cHIXSellJitney, facilitationQty, facilitationSide, buyCustomerAccount, sellCustomerAccount, buyAlgorithmID, sellAlgorithmID, buyCustomerLEI, sellCustomerLEI, buyBrokerLEI, sellBrokerLEI, buyOrderOrigination, sellOrderOrigination, buyRoutingArrangementIndicator, sellRoutingArrangementIndicator, some_bind] <;> rfl

theorem NewOrderSingleCross.taken (record : NewOrderSingleCross) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.settlDate (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 55, 54, 55] record.cHIXBuyAccountType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 55, 54, 56] record.cHIXSellAccountType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 57] record.cHIXBuyAccountID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 48] record.cHIXSellAccountID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 49] record.cHIXBuyRegulationID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 50] record.cHIXSellRegulationID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 51] record.crossType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 49] record.cHIXBuyJitney (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 50] record.cHIXSellJitney (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 53, 48] record.facilitationQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 53, 49] record.facilitationSide (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 49] record.buyCustomerAccount (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 50] record.sellCustomerAccount (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 51] record.buyAlgorithmID (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 52] record.sellAlgorithmID (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 53] record.buyCustomerLEI (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 54] record.sellCustomerLEI (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 55] record.buyBrokerLEI (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 56] record.sellBrokerLEI (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 57] record.buyOrderOrigination (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 48] record.sellOrderOrigination (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator (by decide) (by decide))
                           (paired_none pairing)))))))))))))))))))))))))

structure NewOrderSingleCrossShort where
  settlType : Option (Terminated 1)  -- tag 63
  settlDate : Option (Terminated 1)  -- tag 64
  cHIXBuyAccountType : Terminated 1  -- tag 6767
  cHIXSellAccountType : Terminated 1  -- tag 6768
  cHIXBuyAccountID : Option (Terminated 1)  -- tag 6769
  cHIXSellAccountID : Option (Terminated 1)  -- tag 6770
  cHIXBuyRegulationID : Option (Terminated 1)  -- tag 6771
  cHIXSellRegulationID : Option (Terminated 1)  -- tag 6772
  crossType : Option (Terminated 1)  -- tag 6773
  cHIXBuyJitney : Option (Terminated 1)  -- tag 6781
  cHIXSellJitney : Option (Terminated 1)  -- tag 6782
  facilitationQty : Option (Terminated 1)  -- tag 20050
  facilitationSide : Option (Terminated 1)  -- tag 20051
  buyCustomerAccount : Option (Terminated 1)  -- tag 20201
  sellCustomerAccount : Option (Terminated 1)  -- tag 20202
  buyAlgorithmID : Option (Terminated 1)  -- tag 20203
  sellAlgorithmID : Option (Terminated 1)  -- tag 20204
  buyCustomerLEI : Option (Terminated 1)  -- tag 20205
  sellCustomerLEI : Option (Terminated 1)  -- tag 20206
  buyBrokerLEI : Option (Terminated 1)  -- tag 20207
  sellBrokerLEI : Option (Terminated 1)  -- tag 20208
  buyOrderOrigination : Option (Terminated 1)  -- tag 20209
  sellOrderOrigination : Option (Terminated 1)  -- tag 20210
  buyRoutingArrangementIndicator : Option (Terminated 1)  -- tag 20211
  sellRoutingArrangementIndicator : Option (Terminated 1)  -- tag 20212

def NewOrderSingleCrossShort.parts (record : NewOrderSingleCrossShort) : List Part :=
  [Part.optional [54, 51] record.settlType,
   Part.optional [54, 52] record.settlDate,
   Part.required [54, 55, 54, 55] record.cHIXBuyAccountType,
   Part.required [54, 55, 54, 56] record.cHIXSellAccountType,
   Part.optional [54, 55, 54, 57] record.cHIXBuyAccountID,
   Part.optional [54, 55, 55, 48] record.cHIXSellAccountID,
   Part.optional [54, 55, 55, 49] record.cHIXBuyRegulationID,
   Part.optional [54, 55, 55, 50] record.cHIXSellRegulationID,
   Part.optional [54, 55, 55, 51] record.crossType,
   Part.optional [54, 55, 56, 49] record.cHIXBuyJitney,
   Part.optional [54, 55, 56, 50] record.cHIXSellJitney,
   Part.optional [50, 48, 48, 53, 48] record.facilitationQty,
   Part.optional [50, 48, 48, 53, 49] record.facilitationSide,
   Part.optional [50, 48, 50, 48, 49] record.buyCustomerAccount,
   Part.optional [50, 48, 50, 48, 50] record.sellCustomerAccount,
   Part.optional [50, 48, 50, 48, 51] record.buyAlgorithmID,
   Part.optional [50, 48, 50, 48, 52] record.sellAlgorithmID,
   Part.optional [50, 48, 50, 48, 53] record.buyCustomerLEI,
   Part.optional [50, 48, 50, 48, 54] record.sellCustomerLEI,
   Part.optional [50, 48, 50, 48, 55] record.buyBrokerLEI,
   Part.optional [50, 48, 50, 48, 56] record.sellBrokerLEI,
   Part.optional [50, 48, 50, 48, 57] record.buyOrderOrigination,
   Part.optional [50, 48, 50, 49, 48] record.sellOrderOrigination,
   Part.optional [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator,
   Part.optional [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator]

def NewOrderSingleCrossShort.tags : List (List (List UInt8)) :=
  [[[54, 51]], [[54, 52]], [[54, 55, 54, 55]], [[54, 55, 54, 56]], [[54, 55, 54, 57]], [[54, 55, 55, 48]], [[54, 55, 55, 49]], [[54, 55, 55, 50]], [[54, 55, 55, 51]], [[54, 55, 56, 49]], [[54, 55, 56, 50]], [[50, 48, 48, 53, 48]], [[50, 48, 48, 53, 49]], [[50, 48, 50, 48, 49]], [[50, 48, 50, 48, 50]], [[50, 48, 50, 48, 51]], [[50, 48, 50, 48, 52]], [[50, 48, 50, 48, 53]], [[50, 48, 50, 48, 54]], [[50, 48, 50, 48, 55]], [[50, 48, 50, 48, 56]], [[50, 48, 50, 48, 57]], [[50, 48, 50, 49, 48]], [[50, 48, 50, 49, 49]], [[50, 48, 50, 49, 50]]]

theorem NewOrderSingleCrossShort.shape (record : NewOrderSingleCrossShort) : record.parts.map Part.tags = NewOrderSingleCrossShort.tags := rfl

def NewOrderSingleCrossShort.decode (tokens : List Token) : Option NewOrderSingleCrossShort := do
  let settlType ← readOptional [54, 51] tokens
  let settlDate ← readOptional [54, 52] tokens
  let cHIXBuyAccountType ← readRequired [54, 55, 54, 55] tokens
  let cHIXSellAccountType ← readRequired [54, 55, 54, 56] tokens
  let cHIXBuyAccountID ← readOptional [54, 55, 54, 57] tokens
  let cHIXSellAccountID ← readOptional [54, 55, 55, 48] tokens
  let cHIXBuyRegulationID ← readOptional [54, 55, 55, 49] tokens
  let cHIXSellRegulationID ← readOptional [54, 55, 55, 50] tokens
  let crossType ← readOptional [54, 55, 55, 51] tokens
  let cHIXBuyJitney ← readOptional [54, 55, 56, 49] tokens
  let cHIXSellJitney ← readOptional [54, 55, 56, 50] tokens
  let facilitationQty ← readOptional [50, 48, 48, 53, 48] tokens
  let facilitationSide ← readOptional [50, 48, 48, 53, 49] tokens
  let buyCustomerAccount ← readOptional [50, 48, 50, 48, 49] tokens
  let sellCustomerAccount ← readOptional [50, 48, 50, 48, 50] tokens
  let buyAlgorithmID ← readOptional [50, 48, 50, 48, 51] tokens
  let sellAlgorithmID ← readOptional [50, 48, 50, 48, 52] tokens
  let buyCustomerLEI ← readOptional [50, 48, 50, 48, 53] tokens
  let sellCustomerLEI ← readOptional [50, 48, 50, 48, 54] tokens
  let buyBrokerLEI ← readOptional [50, 48, 50, 48, 55] tokens
  let sellBrokerLEI ← readOptional [50, 48, 50, 48, 56] tokens
  let buyOrderOrigination ← readOptional [50, 48, 50, 48, 57] tokens
  let sellOrderOrigination ← readOptional [50, 48, 50, 49, 48] tokens
  let buyRoutingArrangementIndicator ← readOptional [50, 48, 50, 49, 49] tokens
  let sellRoutingArrangementIndicator ← readOptional [50, 48, 50, 49, 50] tokens
  pure { settlType, settlDate, cHIXBuyAccountType, cHIXSellAccountType, cHIXBuyAccountID, cHIXSellAccountID, cHIXBuyRegulationID, cHIXSellRegulationID, crossType, cHIXBuyJitney, cHIXSellJitney, facilitationQty, facilitationSide, buyCustomerAccount, sellCustomerAccount, buyAlgorithmID, sellAlgorithmID, buyCustomerLEI, sellCustomerLEI, buyBrokerLEI, sellBrokerLEI, buyOrderOrigination, sellOrderOrigination, buyRoutingArrangementIndicator, sellRoutingArrangementIndicator }

theorem NewOrderSingleCrossShort.decode_agrees (record : NewOrderSingleCrossShort) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingleCrossShort.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingleCrossShort.decode tokens = some record := by
  have distinct : NewOrderSingleCrossShort.tags.flatten.Nodup := by decide +kernel
  have settlType := readOptional_part [54, 51] record.settlType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have settlDate := readOptional_part [54, 52] record.settlDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have cHIXBuyAccountType := readRequired_part [54, 55, 54, 55] record.cHIXBuyAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have cHIXSellAccountType := readRequired_part [54, 55, 54, 56] record.cHIXSellAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have cHIXBuyAccountID := readOptional_part [54, 55, 54, 57] record.cHIXBuyAccountID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have cHIXSellAccountID := readOptional_part [54, 55, 55, 48] record.cHIXSellAccountID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have cHIXBuyRegulationID := readOptional_part [54, 55, 55, 49] record.cHIXBuyRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have cHIXSellRegulationID := readOptional_part [54, 55, 55, 50] record.cHIXSellRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have crossType := readOptional_part [54, 55, 55, 51] record.crossType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have cHIXBuyJitney := readOptional_part [54, 55, 56, 49] record.cHIXBuyJitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have cHIXSellJitney := readOptional_part [54, 55, 56, 50] record.cHIXSellJitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have facilitationQty := readOptional_part [50, 48, 48, 53, 48] record.facilitationQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have facilitationSide := readOptional_part [50, 48, 48, 53, 49] record.facilitationSide tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have buyCustomerAccount := readOptional_part [50, 48, 50, 48, 49] record.buyCustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have sellCustomerAccount := readOptional_part [50, 48, 50, 48, 50] record.sellCustomerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have buyAlgorithmID := readOptional_part [50, 48, 50, 48, 51] record.buyAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have sellAlgorithmID := readOptional_part [50, 48, 50, 48, 52] record.sellAlgorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have buyCustomerLEI := readOptional_part [50, 48, 50, 48, 53] record.buyCustomerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have sellCustomerLEI := readOptional_part [50, 48, 50, 48, 54] record.sellCustomerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have buyBrokerLEI := readOptional_part [50, 48, 50, 48, 55] record.buyBrokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have sellBrokerLEI := readOptional_part [50, 48, 50, 48, 56] record.sellBrokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have buyOrderOrigination := readOptional_part [50, 48, 50, 48, 57] record.buyOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have sellOrderOrigination := readOptional_part [50, 48, 50, 49, 48] record.sellOrderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have buyRoutingArrangementIndicator := readOptional_part [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have sellRoutingArrangementIndicator := readOptional_part [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NewOrderSingleCrossShort.decode, settlType, settlDate, cHIXBuyAccountType, cHIXSellAccountType, cHIXBuyAccountID, cHIXSellAccountID, cHIXBuyRegulationID, cHIXSellRegulationID, crossType, cHIXBuyJitney, cHIXSellJitney, facilitationQty, facilitationSide, buyCustomerAccount, sellCustomerAccount, buyAlgorithmID, sellAlgorithmID, buyCustomerLEI, sellCustomerLEI, buyBrokerLEI, sellBrokerLEI, buyOrderOrigination, sellOrderOrigination, buyRoutingArrangementIndicator, sellRoutingArrangementIndicator, some_bind] <;> rfl

theorem NewOrderSingleCrossShort.taken (record : NewOrderSingleCrossShort) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [54, 51] record.settlType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [54, 52] record.settlDate (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [54, 55, 54, 55] record.cHIXBuyAccountType (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [54, 55, 54, 56] record.cHIXSellAccountType (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 57] record.cHIXBuyAccountID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 48] record.cHIXSellAccountID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 49] record.cHIXBuyRegulationID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 50] record.cHIXSellRegulationID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [54, 55, 55, 51] record.crossType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 49] record.cHIXBuyJitney (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 55, 56, 50] record.cHIXSellJitney (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 53, 48] record.facilitationQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [50, 48, 48, 53, 49] record.facilitationSide (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 49] record.buyCustomerAccount (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 50] record.sellCustomerAccount (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 51] record.buyAlgorithmID (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 52] record.sellAlgorithmID (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 53] record.buyCustomerLEI (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 54] record.sellCustomerLEI (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 55] record.buyBrokerLEI (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 56] record.sellBrokerLEI (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 48, 57] record.buyOrderOrigination (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 48] record.sellOrderOrigination (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 49] record.buyRoutingArrangementIndicator (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [50, 48, 50, 49, 50] record.sellRoutingArrangementIndicator (by decide) (by decide))
                           (paired_none pairing)))))))))))))))))))))))))

structure NewOrderSingleOrder where
  account : Option (Terminated 1)  -- tag 1
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  pegDifference : Option (Terminated 1)  -- tag 211
  targetStrategy : Option (Terminated 1)  -- tag 847
  orderOrigination : Option (Terminated 1)  -- tag 1724
  routingArrangementIndicator : Option (Terminated 1)  -- tag 2883
  uMIRAccountType : Terminated 1  -- tag 6750
  jitney : Option (Terminated 1)  -- tag 6757
  gEFEligible : Option (Terminated 1)  -- tag 6759
  uMIRRegulationID : Option (Terminated 1)  -- tag 6763
  tSXNCIB : Option (Terminated 1)  -- tag 6792
  noTradeFeat : Option (Terminated 1)  -- tag 7713
  noTradeKey : Option (Terminated 1)  -- tag 7714
  seekPriceImprovement : Option (Terminated 1)  -- tag 7731
  displayRange : Option (Terminated 1)  -- tag 8020
  customerAccount : Option (Terminated 1)  -- tag 8025
  algorithmID : Option (Terminated 1)  -- tag 8026
  customerLEI : Option (Terminated 1)  -- tag 8027
  brokerLEI : Option (Terminated 1)  -- tag 8028
  conditionalOrder : Option (Terminated 1)  -- tag 23012
  allowConditional : Option (Terminated 1)  -- tag 23013
  firmUpID : Option (Terminated 1)  -- tag 23014
  cXDConnect : Option (Terminated 1)  -- tag 23015
  pureStreamConnect : Option (Terminated 1)  -- tag 23017
  minRate : Option (Terminated 1)  -- tag 27005
  maxRate : Option (Terminated 1)  -- tag 27006

def NewOrderSingleOrder.parts (record : NewOrderSingleOrder) : List Part :=
  [Part.optional [49] record.account,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [50, 49, 49] record.pegDifference,
   Part.optional [56, 52, 55] record.targetStrategy,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 56, 56, 51] record.routingArrangementIndicator,
   Part.required [54, 55, 53, 48] record.uMIRAccountType,
   Part.optional [54, 55, 53, 55] record.jitney,
   Part.optional [54, 55, 53, 57] record.gEFEligible,
   Part.optional [54, 55, 54, 51] record.uMIRRegulationID,
   Part.optional [54, 55, 57, 50] record.tSXNCIB,
   Part.optional [55, 55, 49, 51] record.noTradeFeat,
   Part.optional [55, 55, 49, 52] record.noTradeKey,
   Part.optional [55, 55, 51, 49] record.seekPriceImprovement,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [56, 48, 50, 53] record.customerAccount,
   Part.optional [56, 48, 50, 54] record.algorithmID,
   Part.optional [56, 48, 50, 55] record.customerLEI,
   Part.optional [56, 48, 50, 56] record.brokerLEI,
   Part.optional [50, 51, 48, 49, 50] record.conditionalOrder,
   Part.optional [50, 51, 48, 49, 51] record.allowConditional,
   Part.optional [50, 51, 48, 49, 52] record.firmUpID,
   Part.optional [50, 51, 48, 49, 53] record.cXDConnect,
   Part.optional [50, 51, 48, 49, 55] record.pureStreamConnect,
   Part.optional [50, 55, 48, 48, 53] record.minRate,
   Part.optional [50, 55, 48, 48, 54] record.maxRate]

def NewOrderSingleOrder.tags : List (List (List UInt8)) :=
  [[[49]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[50, 49, 49]], [[56, 52, 55]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 53, 48]], [[54, 55, 53, 55]], [[54, 55, 53, 57]], [[54, 55, 54, 51]], [[54, 55, 57, 50]], [[55, 55, 49, 51]], [[55, 55, 49, 52]], [[55, 55, 51, 49]], [[56, 48, 50, 48]], [[56, 48, 50, 53]], [[56, 48, 50, 54]], [[56, 48, 50, 55]], [[56, 48, 50, 56]], [[50, 51, 48, 49, 50]], [[50, 51, 48, 49, 51]], [[50, 51, 48, 49, 52]], [[50, 51, 48, 49, 53]], [[50, 51, 48, 49, 55]], [[50, 55, 48, 48, 53]], [[50, 55, 48, 48, 54]]]

theorem NewOrderSingleOrder.shape (record : NewOrderSingleOrder) : record.parts.map Part.tags = NewOrderSingleOrder.tags := rfl

def NewOrderSingleOrder.decode (tokens : List Token) : Option NewOrderSingleOrder := do
  let account ← readOptional [49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let pegDifference ← readOptional [50, 49, 49] tokens
  let targetStrategy ← readOptional [56, 52, 55] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let routingArrangementIndicator ← readOptional [50, 56, 56, 51] tokens
  let uMIRAccountType ← readRequired [54, 55, 53, 48] tokens
  let jitney ← readOptional [54, 55, 53, 55] tokens
  let gEFEligible ← readOptional [54, 55, 53, 57] tokens
  let uMIRRegulationID ← readOptional [54, 55, 54, 51] tokens
  let tSXNCIB ← readOptional [54, 55, 57, 50] tokens
  let noTradeFeat ← readOptional [55, 55, 49, 51] tokens
  let noTradeKey ← readOptional [55, 55, 49, 52] tokens
  let seekPriceImprovement ← readOptional [55, 55, 51, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let customerAccount ← readOptional [56, 48, 50, 53] tokens
  let algorithmID ← readOptional [56, 48, 50, 54] tokens
  let customerLEI ← readOptional [56, 48, 50, 55] tokens
  let brokerLEI ← readOptional [56, 48, 50, 56] tokens
  let conditionalOrder ← readOptional [50, 51, 48, 49, 50] tokens
  let allowConditional ← readOptional [50, 51, 48, 49, 51] tokens
  let firmUpID ← readOptional [50, 51, 48, 49, 52] tokens
  let cXDConnect ← readOptional [50, 51, 48, 49, 53] tokens
  let pureStreamConnect ← readOptional [50, 51, 48, 49, 55] tokens
  let minRate ← readOptional [50, 55, 48, 48, 53] tokens
  let maxRate ← readOptional [50, 55, 48, 48, 54] tokens
  pure { account, minQty, maxFloor, expireTime, pegDifference, targetStrategy, orderOrigination, routingArrangementIndicator, uMIRAccountType, jitney, gEFEligible, uMIRRegulationID, tSXNCIB, noTradeFeat, noTradeKey, seekPriceImprovement, displayRange, customerAccount, algorithmID, customerLEI, brokerLEI, conditionalOrder, allowConditional, firmUpID, cXDConnect, pureStreamConnect, minRate, maxRate }

theorem NewOrderSingleOrder.decode_agrees (record : NewOrderSingleOrder) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingleOrder.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingleOrder.decode tokens = some record := by
  have distinct : NewOrderSingleOrder.tags.flatten.Nodup := by decide +kernel
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have pegDifference := readOptional_part [50, 49, 49] record.pegDifference tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetStrategy := readOptional_part [56, 52, 55] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have routingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.routingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have uMIRAccountType := readRequired_part [54, 55, 53, 48] record.uMIRAccountType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have jitney := readOptional_part [54, 55, 53, 55] record.jitney tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have gEFEligible := readOptional_part [54, 55, 53, 57] record.gEFEligible tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have tSXNCIB := readOptional_part [54, 55, 57, 50] record.tSXNCIB tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have noTradeFeat := readOptional_part [55, 55, 49, 51] record.noTradeFeat tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have noTradeKey := readOptional_part [55, 55, 49, 52] record.noTradeKey tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have seekPriceImprovement := readOptional_part [55, 55, 51, 49] record.seekPriceImprovement tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have customerAccount := readOptional_part [56, 48, 50, 53] record.customerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have algorithmID := readOptional_part [56, 48, 50, 54] record.algorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have customerLEI := readOptional_part [56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have brokerLEI := readOptional_part [56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have conditionalOrder := readOptional_part [50, 51, 48, 49, 50] record.conditionalOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have allowConditional := readOptional_part [50, 51, 48, 49, 51] record.allowConditional tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have firmUpID := readOptional_part [50, 51, 48, 49, 52] record.firmUpID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have cXDConnect := readOptional_part [50, 51, 48, 49, 53] record.cXDConnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have pureStreamConnect := readOptional_part [50, 51, 48, 49, 55] record.pureStreamConnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have minRate := readOptional_part [50, 55, 48, 48, 53] record.minRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have maxRate := readOptional_part [50, 55, 48, 48, 54] record.maxRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  simp only [NewOrderSingleOrder.decode, account, minQty, maxFloor, expireTime, pegDifference, targetStrategy, orderOrigination, routingArrangementIndicator, uMIRAccountType, jitney, gEFEligible, uMIRRegulationID, tSXNCIB, noTradeFeat, noTradeKey, seekPriceImprovement, displayRange, customerAccount, algorithmID, customerLEI, brokerLEI, conditionalOrder, allowConditional, firmUpID, cXDConnect, pureStreamConnect, minRate, maxRate, some_bind] <;> rfl

theorem NewOrderSingleOrder.taken (record : NewOrderSingleOrder) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [50, 49, 49] record.pegDifference (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [56, 52, 55] record.targetStrategy (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.orderOrigination (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 51] record.routingArrangementIndicator (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [54, 55, 53, 48] record.uMIRAccountType (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 55] record.jitney (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [54, 55, 53, 57] record.gEFEligible (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 51] record.uMIRRegulationID (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [54, 55, 57, 50] record.tSXNCIB (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [55, 55, 49, 51] record.noTradeFeat (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [55, 55, 49, 52] record.noTradeKey (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [55, 55, 51, 49] record.seekPriceImprovement (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.displayRange (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 53] record.customerAccount (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 54] record.algorithmID (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 55] record.customerLEI (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 56] record.brokerLEI (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 50] record.conditionalOrder (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 51] record.allowConditional (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 52] record.firmUpID (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 53] record.cXDConnect (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 55] record.pureStreamConnect (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48, 48, 53] record.minRate (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48, 48, 54] record.maxRate (by decide) (by decide))
                              (paired_none pairing))))))))))))))))))))))))))))

structure OrderCancelReplaceRequest where
  clOrdID : Terminated 1  -- tag 11
  execInst : Option (Terminated 1)  -- tag 18
  handlInst : Terminated 1  -- tag 21
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  origClOrdID : Terminated 1  -- tag 41
  price : Option (Terminated 1)  -- tag 44
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  timeInForce : Option (Terminated 1)  -- tag 59
  transactTime : Terminated 1  -- tag 60
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  expireTime : Option (Terminated 1)  -- tag 126
  targetStrategy : Option (Terminated 1)  -- tag 847
  orderOrigination : Option (Terminated 1)  -- tag 1724
  routingArrangementIndicator : Option (Terminated 1)  -- tag 2883
  uMIRRegulationID : Option (Terminated 1)  -- tag 6763
  anonymous : Option (Terminated 1)  -- tag 6761
  displayRange : Option (Terminated 1)  -- tag 8020
  customerAccount : Option (Terminated 1)  -- tag 8025
  algorithmID : Option (Terminated 1)  -- tag 8026
  customerLEI : Option (Terminated 1)  -- tag 8027
  brokerLEI : Option (Terminated 1)  -- tag 8028
  conditionalOrder : Option (Terminated 1)  -- tag 23012
  allowConditional : Option (Terminated 1)  -- tag 23013
  cXDConnect : Option (Terminated 1)  -- tag 23015
  pureStreamConnect : Option (Terminated 1)  -- tag 23017
  minRate : Option (Terminated 1)  -- tag 27005
  maxRate : Option (Terminated 1)  -- tag 27006

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [49, 56] record.execInst,
   Part.required [50, 49] record.handlInst,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.required [52, 49] record.origClOrdID,
   Part.optional [52, 52] record.price,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.optional [53, 57] record.timeInForce,
   Part.required [54, 48] record.transactTime,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 50, 54] record.expireTime,
   Part.optional [56, 52, 55] record.targetStrategy,
   Part.optional [49, 55, 50, 52] record.orderOrigination,
   Part.optional [50, 56, 56, 51] record.routingArrangementIndicator,
   Part.optional [54, 55, 54, 51] record.uMIRRegulationID,
   Part.optional [54, 55, 54, 49] record.anonymous,
   Part.optional [56, 48, 50, 48] record.displayRange,
   Part.optional [56, 48, 50, 53] record.customerAccount,
   Part.optional [56, 48, 50, 54] record.algorithmID,
   Part.optional [56, 48, 50, 55] record.customerLEI,
   Part.optional [56, 48, 50, 56] record.brokerLEI,
   Part.optional [50, 51, 48, 49, 50] record.conditionalOrder,
   Part.optional [50, 51, 48, 49, 51] record.allowConditional,
   Part.optional [50, 51, 48, 49, 53] record.cXDConnect,
   Part.optional [50, 51, 48, 49, 55] record.pureStreamConnect,
   Part.optional [50, 55, 48, 48, 53] record.minRate,
   Part.optional [50, 55, 48, 48, 54] record.maxRate]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[49, 56]], [[50, 49]], [[51, 56]], [[52, 48]], [[52, 49]], [[52, 52]], [[53, 52]], [[53, 53]], [[53, 57]], [[54, 48]], [[49, 49, 48]], [[49, 49, 49]], [[49, 50, 54]], [[56, 52, 55]], [[49, 55, 50, 52]], [[50, 56, 56, 51]], [[54, 55, 54, 51]], [[54, 55, 54, 49]], [[56, 48, 50, 48]], [[56, 48, 50, 53]], [[56, 48, 50, 54]], [[56, 48, 50, 55]], [[56, 48, 50, 56]], [[50, 51, 48, 49, 50]], [[50, 51, 48, 49, 51]], [[50, 51, 48, 49, 53]], [[50, 51, 48, 49, 55]], [[50, 55, 48, 48, 53]], [[50, 55, 48, 48, 54]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let execInst ← readOptional [49, 56] tokens
  let handlInst ← readRequired [50, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let price ← readOptional [52, 52] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let transactTime ← readRequired [54, 48] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let targetStrategy ← readOptional [56, 52, 55] tokens
  let orderOrigination ← readOptional [49, 55, 50, 52] tokens
  let routingArrangementIndicator ← readOptional [50, 56, 56, 51] tokens
  let uMIRRegulationID ← readOptional [54, 55, 54, 51] tokens
  let anonymous ← readOptional [54, 55, 54, 49] tokens
  let displayRange ← readOptional [56, 48, 50, 48] tokens
  let customerAccount ← readOptional [56, 48, 50, 53] tokens
  let algorithmID ← readOptional [56, 48, 50, 54] tokens
  let customerLEI ← readOptional [56, 48, 50, 55] tokens
  let brokerLEI ← readOptional [56, 48, 50, 56] tokens
  let conditionalOrder ← readOptional [50, 51, 48, 49, 50] tokens
  let allowConditional ← readOptional [50, 51, 48, 49, 51] tokens
  let cXDConnect ← readOptional [50, 51, 48, 49, 53] tokens
  let pureStreamConnect ← readOptional [50, 51, 48, 49, 55] tokens
  let minRate ← readOptional [50, 55, 48, 48, 53] tokens
  let maxRate ← readOptional [50, 55, 48, 48, 54] tokens
  pure { clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, targetStrategy, orderOrigination, routingArrangementIndicator, uMIRRegulationID, anonymous, displayRange, customerAccount, algorithmID, customerLEI, brokerLEI, conditionalOrder, allowConditional, cXDConnect, pureStreamConnect, minRate, maxRate }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readRequired_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have targetStrategy := readOptional_part [56, 52, 55] record.targetStrategy tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have orderOrigination := readOptional_part [49, 55, 50, 52] record.orderOrigination tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have routingArrangementIndicator := readOptional_part [50, 56, 56, 51] record.routingArrangementIndicator tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have uMIRRegulationID := readOptional_part [54, 55, 54, 51] record.uMIRRegulationID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have anonymous := readOptional_part [54, 55, 54, 49] record.anonymous tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have displayRange := readOptional_part [56, 48, 50, 48] record.displayRange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have customerAccount := readOptional_part [56, 48, 50, 53] record.customerAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have algorithmID := readOptional_part [56, 48, 50, 54] record.algorithmID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have customerLEI := readOptional_part [56, 48, 50, 55] record.customerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have brokerLEI := readOptional_part [56, 48, 50, 56] record.brokerLEI tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have conditionalOrder := readOptional_part [50, 51, 48, 49, 50] record.conditionalOrder tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have allowConditional := readOptional_part [50, 51, 48, 49, 51] record.allowConditional tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have cXDConnect := readOptional_part [50, 51, 48, 49, 53] record.cXDConnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have pureStreamConnect := readOptional_part [50, 51, 48, 49, 55] record.pureStreamConnect tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have minRate := readOptional_part [50, 55, 48, 48, 53] record.minRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have maxRate := readOptional_part [50, 55, 48, 48, 54] record.maxRate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, clOrdID, execInst, handlInst, orderQty, ordType, origClOrdID, price, side, symbol, timeInForce, transactTime, minQty, maxFloor, expireTime, targetStrategy, orderOrigination, routingArrangementIndicator, uMIRRegulationID, anonymous, displayRange, customerAccount, algorithmID, customerLEI, brokerLEI, conditionalOrder, allowConditional, cXDConnect, pureStreamConnect, minRate, maxRate, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [50, 49] record.handlInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [56, 52, 55] record.targetStrategy (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 55, 50, 52] record.orderOrigination (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [50, 56, 56, 51] record.routingArrangementIndicator (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 51] record.uMIRRegulationID (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [54, 55, 54, 49] record.anonymous (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 48] record.displayRange (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 53] record.customerAccount (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 54] record.algorithmID (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 55] record.customerLEI (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [56, 48, 50, 56] record.brokerLEI (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 50] record.conditionalOrder (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 51] record.allowConditional (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 53] record.cXDConnect (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [50, 51, 48, 49, 55] record.pureStreamConnect (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48, 48, 53] record.minRate (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [50, 55, 48, 48, 54] record.maxRate (by decide) (by decide))
                                (paired_none pairing))))))))))))))))))))))))))))))

structure OrderCancelRequest where
  clOrdID : Terminated 1  -- tag 11
  orderQty : Terminated 1  -- tag 38
  origClOrdID : Terminated 1  -- tag 41
  side : Terminated 1  -- tag 54
  symbol : Terminated 1  -- tag 55
  transactTime : Terminated 1  -- tag 60

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 49] record.origClOrdID,
   Part.required [53, 52] record.side,
   Part.required [53, 53] record.symbol,
   Part.required [54, 48] record.transactTime]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[51, 56]], [[52, 49]], [[53, 52]], [[53, 53]], [[54, 48]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let clOrdID ← readRequired [49, 49] tokens
  let orderQty ← readRequired [51, 56] tokens
  let origClOrdID ← readRequired [52, 49] tokens
  let side ← readRequired [53, 52] tokens
  let symbol ← readRequired [53, 53] tokens
  let transactTime ← readRequired [54, 48] tokens
  pure { clOrdID, orderQty, origClOrdID, side, symbol, transactTime }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have transactTime := readRequired_part [54, 48] record.transactTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, clOrdID, orderQty, origClOrdID, side, symbol, transactTime, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [54, 48] record.transactTime (by decide) (by decide))
        (paired_none pairing))))))

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

inductive Message where
  | heartbeat (header : Header) (r0 : Heartbeat)
  | logon (header : Header) (r0 : Logon)
  | logout (header : Header) (r0 : Logout)
  | marketParticipantCommand (header : Header) (r0 : MarketParticipantCommand)
  | newOrderSingleCross (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCross)
  | newOrderSingleCrossShort (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCrossShort)
  | newOrderSingleOrder (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[56], [57]] : List (List UInt8))}) (r0 : NewOrderSingle) (r1 : NewOrderSingleOrder)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .marketParticipantCommand header r0 => ⟨[51, 53], [77, 67]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingleCross header r0 r1 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts)
  | .newOrderSingleCrossShort header r0 r1 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts)
  | .newOrderSingleOrder header k0 r0 r1 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts ++ [Part.required [53, 52] k0.1] ++ r1.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .reject header r0 => ⟨[51, 53], [51]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .resendRequest header r0 => ⟨[51, 53], [50]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .sequenceReset header r0 => ⟨[51, 53], [52]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .testRequest header r0 => ⟨[51, 53], [49]⟩ :: encodeParts (header.parts ++ r0.parts)

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
      else if token.value = [77, 67] then
        if known (Header.tags ++ MarketParticipantCommand.tags) rest then do
          let header ← Header.decode rest
          let r0 ← MarketParticipantCommand.decode rest
          pure (.marketParticipantCommand header r0)
        else none
      else if token.value = [68] then
        match readRequired [53, 52] rest with
        | none => none
        | some key =>
          if h0_0 : key.val = [56] then
            if known (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCross.tags) rest then do
              let header ← Header.decode rest
              let r0 ← NewOrderSingle.decode rest
              let r1 ← NewOrderSingleCross.decode rest
              pure (.newOrderSingleCross header r0 r1)
            else none
          else if h0_1 : key.val = [57] then
            if known (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCrossShort.tags) rest then do
              let header ← Header.decode rest
              let r0 ← NewOrderSingle.decode rest
              let r1 ← NewOrderSingleCrossShort.decode rest
              pure (.newOrderSingleCrossShort header r0 r1)
            else none
          else let k0 : {v : Terminated 1 // v.val ∉ ([[56], [57]] : List (List UInt8))} := ⟨key, by simp [h0_0, h0_1]⟩
          if known (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleOrder.tags) rest then do
            let header ← Header.decode rest
            let r0 ← NewOrderSingle.decode rest
            let r1 ← NewOrderSingleOrder.decode rest
            pure (.newOrderSingleOrder header k0 r0 r1)
          else none
      else if token.value = [71] then
        if known (Header.tags ++ OrderCancelReplaceRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelReplaceRequest.decode rest
          pure (.orderCancelReplaceRequest header r0)
        else none
      else if token.value = [70] then
        if known (Header.tags ++ OrderCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderCancelRequest.decode rest
          pure (.orderCancelRequest header r0)
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
      else none
    else none

theorem Message.decode_heartbeat (header : Header) (r0 : Heartbeat) :
    Message.decode (Message.tokens (.heartbeat header r0)) = some (.heartbeat header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) rfl rfl (by decide +kernel))
  have c1 := Heartbeat.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Heartbeat.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Heartbeat.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_logon (header : Header) (r0 : Logon) :
    Message.decode (Message.tokens (.logon header r0)) = some (.logon header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) rfl rfl (by decide +kernel))
  have c1 := Logon.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logon.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logon.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_logout (header : Header) (r0 : Logout) :
    Message.decode (Message.tokens (.logout header r0)) = some (.logout header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) rfl rfl (by decide +kernel))
  have c1 := Logout.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Logout.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Logout.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_marketParticipantCommand (header : Header) (r0 : MarketParticipantCommand) :
    Message.decode (Message.tokens (.marketParticipantCommand header r0)) = some (.marketParticipantCommand header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (MarketParticipantCommand.tags) rfl rfl (by decide +kernel))
  have c1 := MarketParticipantCommand.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (MarketParticipantCommand.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ MarketParticipantCommand.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingleCross (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCross) :
    Message.decode (Message.tokens (.newOrderSingleCross header r0 r1)) = some (.newOrderSingleCross header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts) ([]) (Header.tags) (NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCross.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags) (NewOrderSingle.tags) ([[[53, 52]]] ++ NewOrderSingleCross.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 52] ⟨[56], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 52] ⟨[56], by decide⟩]) (r1.parts) (Header.tags ++ NewOrderSingle.tags) ([[[53, 52]]]) (NewOrderSingleCross.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := NewOrderSingleCross.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩]) (r1.parts) ([]) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]]) (NewOrderSingleCross.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCross.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingleCrossShort (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCrossShort) :
    Message.decode (Message.tokens (.newOrderSingleCrossShort header r0 r1)) = some (.newOrderSingleCrossShort header r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts) ([]) (Header.tags) (NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCrossShort.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts) (Header.tags) (NewOrderSingle.tags) ([[[53, 52]]] ++ NewOrderSingleCrossShort.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 52] ⟨[57], by decide⟩ _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 52] ⟨[57], by decide⟩]) (r1.parts) (Header.tags ++ NewOrderSingle.tags) ([[[53, 52]]]) (NewOrderSingleCrossShort.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := NewOrderSingleCrossShort.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩]) (r1.parts) ([]) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]]) (NewOrderSingleCrossShort.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleCrossShort.tags) rfl
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingleOrder (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[56], [57]] : List (List UInt8))}) (r0 : NewOrderSingle) (r1 : NewOrderSingleOrder) :
    Message.decode (Message.tokens (.newOrderSingleOrder header k0 r0 r1)) = some (.newOrderSingleOrder header k0 r0 r1) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts ++ [Part.required [53, 52] k0.1] ++ r1.parts) ([]) (Header.tags) (NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleOrder.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([Part.required [53, 52] k0.1] ++ r1.parts) (Header.tags) (NewOrderSingle.tags) ([[[53, 52]]] ++ NewOrderSingleOrder.tags) rfl rfl (by decide +kernel))
  have c2 := readRequired_part [53, 52] k0.1 _ (((agrees_slice (header.parts ++ r0.parts) ([Part.required [53, 52] k0.1]) (r1.parts) (Header.tags ++ NewOrderSingle.tags) ([[[53, 52]]]) (NewOrderSingleOrder.tags) rfl rfl (by decide +kernel)) _ (by decide +kernel)).trans rfl)
  have c3 := NewOrderSingleOrder.decode_agrees r1 _ (agrees_slice (header.parts ++ r0.parts ++ [Part.required [53, 52] k0.1]) (r1.parts) ([]) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]]) (NewOrderSingleOrder.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts ++ [Part.required [53, 52] k0.1] ++ r1.parts) (Header.tags ++ NewOrderSingle.tags ++ [[[53, 52]]] ++ NewOrderSingleOrder.tags) rfl
  have e0 := k0.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at e0
  simp only [List.nil_append, List.append_nil, List.append_assoc] at c0 c1 c2 c3 knows
  simp +decide only [Message.tokens, Message.decode, List.append_assoc, knows, c0, c1, c2, c3, ite_true, ite_false, dite_true, dite_false, e0, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_reject (header : Header) (r0 : Reject) :
    Message.decode (Message.tokens (.reject header r0)) = some (.reject header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) rfl rfl (by decide +kernel))
  have c1 := Reject.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (Reject.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ Reject.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_resendRequest (header : Header) (r0 : ResendRequest) :
    Message.decode (Message.tokens (.resendRequest header r0)) = some (.resendRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) rfl rfl (by decide +kernel))
  have c1 := ResendRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (ResendRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ ResendRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_sequenceReset (header : Header) (r0 : SequenceReset) :
    Message.decode (Message.tokens (.sequenceReset header r0)) = some (.sequenceReset header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) rfl rfl (by decide +kernel))
  have c1 := SequenceReset.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (SequenceReset.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ SequenceReset.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_testRequest (header : Header) (r0 : TestRequest) :
    Message.decode (Message.tokens (.testRequest header r0)) = some (.testRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) rfl rfl (by decide +kernel))
  have c1 := TestRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (TestRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ TestRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, dite_true, dite_false, some_bind] <;> rfl

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | marketParticipantCommand header r0 => exact Message.decode_marketParticipantCommand header r0
  | newOrderSingleCross header r0 r1 => exact Message.decode_newOrderSingleCross header r0 r1
  | newOrderSingleCrossShort header r0 r1 => exact Message.decode_newOrderSingleCrossShort header r0 r1
  | newOrderSingleOrder header k0 r0 r1 => exact Message.decode_newOrderSingleOrder header k0 r0 r1
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | reject header r0 => exact Message.decode_reject header r0
  | resendRequest header r0 => exact Message.decode_resendRequest header r0
  | sequenceReset header r0 => exact Message.decode_sequenceReset header r0
  | testRequest header r0 => exact Message.decode_testRequest header r0

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

theorem Message.decodeBytes_marketParticipantCommand (header : Header) (r0 : MarketParticipantCommand) :
    Message.decodeBytes (Message.encode (.marketParticipantCommand header r0)) = some (.marketParticipantCommand header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [77, 67]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (MarketParticipantCommand.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_marketParticipantCommand header r0

theorem Message.decodeBytes_newOrderSingleCross (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCross) :
    Message.decodeBytes (Message.encode (.newOrderSingleCross header r0 r1)) = some (.newOrderSingleCross header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [53, 52] ⟨[56], by decide⟩] ++ r1.parts) (NewOrderSingle.taken r0) (paired_parts pairing ([Part.required [53, 52] ⟨[56], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [53, 52] ⟨[56], by decide⟩) [] (paired_required pairing [53, 52] ⟨[56], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (NewOrderSingleCross.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingleCross header r0 r1

theorem Message.decodeBytes_newOrderSingleCrossShort (header : Header) (r0 : NewOrderSingle) (r1 : NewOrderSingleCrossShort) :
    Message.decodeBytes (Message.encode (.newOrderSingleCrossShort header r0 r1)) = some (.newOrderSingleCrossShort header r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [53, 52] ⟨[57], by decide⟩] ++ r1.parts) (NewOrderSingle.taken r0) (paired_parts pairing ([Part.required [53, 52] ⟨[57], by decide⟩]) (r1.parts) (paired_cons pairing (Part.required [53, 52] ⟨[57], by decide⟩) [] (paired_required pairing [53, 52] ⟨[57], by decide⟩ (by decide) (by decide)) (paired_none pairing)) (NewOrderSingleCrossShort.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingleCrossShort header r0 r1

theorem Message.decodeBytes_newOrderSingleOrder (header : Header) (k0 : {v : Terminated 1 // v.val ∉ ([[56], [57]] : List (List UInt8))}) (r0 : NewOrderSingle) (r1 : NewOrderSingleOrder) :
    Message.decodeBytes (Message.encode (.newOrderSingleOrder header k0 r0 r1)) = some (.newOrderSingleOrder header k0 r0 r1) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts ++ [Part.required [53, 52] k0.1] ++ r1.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts ++ [Part.required [53, 52] k0.1] ++ r1.parts) (Header.taken header) (paired_parts pairing (r0.parts) ([Part.required [53, 52] k0.1] ++ r1.parts) (NewOrderSingle.taken r0) (paired_parts pairing ([Part.required [53, 52] k0.1]) (r1.parts) (paired_cons pairing (Part.required [53, 52] k0.1) [] (paired_required pairing [53, 52] k0.1 (by decide) (by decide)) (paired_none pairing)) (NewOrderSingleOrder.taken r1))))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingleOrder header k0 r0 r1

theorem Message.decodeBytes_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decodeBytes (Message.encode (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [71]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelReplaceRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelReplaceRequest header r0

theorem Message.decodeBytes_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decodeBytes (Message.encode (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [70]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderCancelRequest header r0

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

theorem Message.decodeBytes_encode (message : Message) : Message.decodeBytes message.encode = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decodeBytes_heartbeat header r0
  | logon header r0 => exact Message.decodeBytes_logon header r0
  | logout header r0 => exact Message.decodeBytes_logout header r0
  | marketParticipantCommand header r0 => exact Message.decodeBytes_marketParticipantCommand header r0
  | newOrderSingleCross header r0 r1 => exact Message.decodeBytes_newOrderSingleCross header r0 r1
  | newOrderSingleCrossShort header r0 r1 => exact Message.decodeBytes_newOrderSingleCrossShort header r0 r1
  | newOrderSingleOrder header k0 r0 r1 => exact Message.decodeBytes_newOrderSingleOrder header k0 r0 r1
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue fixes it: FIX.4.2 -/
def begin : List UInt8 := [56, 61, 70, 73, 88, 46, 52, 46, 50, 1]

def Packet.encode (message : Message) : List UInt8 := encodeFix begin Message.encode message

def Packet.decode (bytes : List UInt8) : Option (Message × List UInt8) := decodeFix begin Message.decodeBytes bytes

theorem Packet.decode_encode (message : Message) (rest : List UInt8) :
    Packet.decode (Packet.encode message ++ rest) = some (message, rest) :=
  decodeFix_encodeFix begin Message.encode Message.decodeBytes Message.decodeBytes_encode message rest

end Omi.NasdaqNasdaqcanadaOrderentryFixV42165Client
