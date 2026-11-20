import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Order Entry v2.0.f, Client messages

Generated from the Fix model, with the proofs its structure calls for: every message decodes back to
what was encoded; MsgType, and each field a message's arms are chosen by, selects the message it names;
BodyLength is written from the body and CheckSum from every byte before it.

Fields are read by tag wherever they stand, as Fix allows, and written in the order the model lists
them. A repeating group keeps its order: its count, then each entry led by its delimiter. A message
carrying a tag its model does not list is not read. Values are kept as their text, byte for byte.

License: MIT No Attribution
-/

namespace Omi.NasdaqNtxoptionsOrderentryFixV20FClient

/-- No field of this tree is data, so every value ends at the separator -/
def pairing : Pairing := []

structure Header where
  msgSeqNum : Terminated 1  -- tag 34
  senderCompID : Terminated 1  -- tag 49
  targetCompID : Terminated 1  -- tag 56
  sendingTime : Terminated 1  -- tag 52
  senderSubID : Option (Terminated 1)  -- tag 50
  targetSubID : Option (Terminated 1)  -- tag 57
  possDupFlag : Option (Terminated 1)  -- tag 43
  possResend : Option (Terminated 1)  -- tag 97
  origSendingTime : Option (Terminated 1)  -- tag 122

def Header.parts (record : Header) : List Part :=
  [Part.required [51, 52] record.msgSeqNum,
   Part.required [52, 57] record.senderCompID,
   Part.required [53, 54] record.targetCompID,
   Part.required [53, 50] record.sendingTime,
   Part.optional [53, 48] record.senderSubID,
   Part.optional [53, 55] record.targetSubID,
   Part.optional [52, 51] record.possDupFlag,
   Part.optional [57, 55] record.possResend,
   Part.optional [49, 50, 50] record.origSendingTime]

def Header.tags : List (List (List UInt8)) :=
  [[[51, 52]], [[52, 57]], [[53, 54]], [[53, 50]], [[53, 48]], [[53, 55]], [[52, 51]], [[57, 55]], [[49, 50, 50]]]

theorem Header.shape (record : Header) : record.parts.map Part.tags = Header.tags := rfl

def Header.decode (tokens : List Token) : Option Header := do
  let msgSeqNum ← readRequired [51, 52] tokens
  let senderCompID ← readRequired [52, 57] tokens
  let targetCompID ← readRequired [53, 54] tokens
  let sendingTime ← readRequired [53, 50] tokens
  let senderSubID ← readOptional [53, 48] tokens
  let targetSubID ← readOptional [53, 55] tokens
  let possDupFlag ← readOptional [52, 51] tokens
  let possResend ← readOptional [57, 55] tokens
  let origSendingTime ← readOptional [49, 50, 50] tokens
  pure { msgSeqNum, senderCompID, targetCompID, sendingTime, senderSubID, targetSubID, possDupFlag, possResend, origSendingTime }

theorem Header.decode_agrees (record : Header) (tokens : List Token)
    (agrees : ∀ tags ∈ Header.tags, select tags tokens = select tags (encodeParts record.parts)) :
    Header.decode tokens = some record := by
  have distinct : Header.tags.flatten.Nodup := by decide +kernel
  have msgSeqNum := readRequired_part [51, 52] record.msgSeqNum tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have senderCompID := readRequired_part [52, 57] record.senderCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have targetCompID := readRequired_part [53, 54] record.targetCompID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have sendingTime := readRequired_part [53, 50] record.sendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have senderSubID := readOptional_part [53, 48] record.senderSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have targetSubID := readOptional_part [53, 55] record.targetSubID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have possDupFlag := readOptional_part [52, 51] record.possDupFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have possResend := readOptional_part [57, 55] record.possResend tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have origSendingTime := readOptional_part [49, 50, 50] record.origSendingTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  simp only [Header.decode, msgSeqNum, senderCompID, targetCompID, sendingTime, senderSubID, targetSubID, possDupFlag, possResend, origSendingTime, some_bind] <;> rfl

theorem Header.taken (record : Header) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [51, 52] record.msgSeqNum (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [52, 57] record.senderCompID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 54] record.targetCompID (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 50] record.sendingTime (by decide) (by decide))
      (paired_cons pairing _ _ (paired_optional pairing [53, 48] record.senderSubID (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [53, 55] record.targetSubID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 51] record.possDupFlag (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [57, 55] record.possResend (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 50, 50] record.origSendingTime (by decide) (by decide))
           (paired_none pairing)))))))))

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

structure NoOrders where
  listSeqNo : Terminated 1  -- tag 67
  clOrdID : Terminated 1  -- tag 11
  handlInst : Option (Terminated 1)  -- tag 21
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  clientID : Option (Terminated 1)  -- tag 109
  account : Option (Terminated 1)  -- tag 1
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Terminated 1  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  text : Option (Terminated 1)  -- tag 58
  openClose : Terminated 1  -- tag 77
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  clearingAccount : Option (Terminated 1)  -- tag 440
  securityExchange : Option (Terminated 1)  -- tag 207
  clearingFirm : Option (Terminated 1)  -- tag 439
  allocAccount : Option (Terminated 1)  -- tag 79

def NoOrders.parts (record : NoOrders) : List Part :=
  [Part.required [54, 55] record.listSeqNo,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49] record.handlInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49] record.account,
   Part.optional [49, 56] record.execInst,
   Part.required [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [53, 56] record.text,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57] record.allocAccount]

def NoOrders.tags : List (List (List UInt8)) :=
  [[[54, 55]], [[49, 49]], [[50, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 48, 57]], [[49]], [[49, 56]], [[53, 57]], [[52, 55]], [[53, 56]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[52, 52, 48]], [[50, 48, 55]], [[52, 51, 57]], [[55, 57]]]

theorem NoOrders.shape (record : NoOrders) : record.parts.map Part.tags = NoOrders.tags := rfl

def NoOrders.decode (tokens : List Token) : Option NoOrders := do
  let listSeqNo ← readRequired [54, 55] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let handlInst ← readOptional [50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let account ← readOptional [49] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readRequired [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let text ← readOptional [53, 56] tokens
  let openClose ← readRequired [55, 55] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let allocAccount ← readOptional [55, 57] tokens
  pure { listSeqNo, clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, account, execInst, timeInForce, rule80A, text, openClose, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, clearingAccount, securityExchange, clearingFirm, allocAccount }

theorem NoOrders.decode_agrees (record : NoOrders) (tokens : List Token)
    (agrees : ∀ tags ∈ NoOrders.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NoOrders.decode tokens = some record := by
  have distinct : NoOrders.tags.flatten.Nodup := by decide +kernel
  have listSeqNo := readRequired_part [54, 55] record.listSeqNo tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readRequired_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [NoOrders.decode, listSeqNo, clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, account, execInst, timeInForce, rule80A, text, openClose, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, clearingAccount, securityExchange, clearingFirm, allocAccount, some_bind] <;> rfl

theorem NoOrders.taken (record : NoOrders) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [54, 55] record.listSeqNo (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 49] record.handlInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [53, 57] record.timeInForce (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
                           (paired_none pairing)))))))))))))))))))))))))

def NoOrders.members : List (List UInt8) := NoOrders.tags.flatten

def NoOrders.encode (entry : NoOrders) : List Token := encodeParts entry.parts

theorem NoOrders.decode_encode (entry : NoOrders) : NoOrders.decode entry.encode = some entry :=
  NoOrders.decode_agrees entry _ (fun _ _ => rfl)

theorem NoOrders.within (entry : NoOrders) : ∀ token ∈ entry.encode, token.tag ∈ NoOrders.members := by
  intro token inside
  have := encodeParts_within entry.parts token inside
  rwa [NoOrders.shape] at this

theorem NoOrders.led (entry : NoOrders) : Lead [54, 55] entry.encode :=
  lead_parts [54, 55] entry.listSeqNo _ NoOrders.tags.tail rfl (by decide +kernel)

structure NewOrderList where
  auctionType : Terminated 1  -- tag 9373
  nWTOrdType : Option (Terminated 1)  -- tag 9371
  nWTPrice : Option (Terminated 1)  -- tag 9372
  brokerPCT : Option (Terminated 1)  -- tag 9204
  noOrders : List NoOrders  -- tag 73

def NewOrderList.parts (record : NewOrderList) : List Part :=
  [Part.required [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 49] record.nWTOrdType,
   Part.optional [57, 51, 55, 50] record.nWTPrice,
   Part.optional [57, 50, 48, 52] record.brokerPCT,
   Part.group [55, 51] NoOrders.members NoOrders.encode NoOrders.within record.noOrders]

def NewOrderList.tags : List (List (List UInt8)) :=
  [[[57, 51, 55, 51]], [[57, 51, 55, 49]], [[57, 51, 55, 50]], [[57, 50, 48, 52]], [55, 51] :: NoOrders.members]

theorem NewOrderList.shape (record : NewOrderList) : record.parts.map Part.tags = NewOrderList.tags := rfl

def NewOrderList.decode (tokens : List Token) : Option NewOrderList := do
  let auctionType ← readRequired [57, 51, 55, 51] tokens
  let nWTOrdType ← readOptional [57, 51, 55, 49] tokens
  let nWTPrice ← readOptional [57, 51, 55, 50] tokens
  let brokerPCT ← readOptional [57, 50, 48, 52] tokens
  let noOrders ← readGroup [55, 51] [54, 55] NoOrders.members NoOrders.decode tokens
  pure { auctionType, nWTOrdType, nWTPrice, brokerPCT, noOrders }

theorem NewOrderList.decode_agrees (record : NewOrderList) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderList.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderList.decode tokens = some record := by
  have distinct : NewOrderList.tags.flatten.Nodup := by decide +kernel
  have auctionType := readRequired_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have nWTOrdType := readOptional_part [57, 51, 55, 49] record.nWTOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have nWTPrice := readOptional_part [57, 51, 55, 50] record.nWTPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have brokerPCT := readOptional_part [57, 50, 48, 52] record.brokerPCT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have noOrders := readGroup_part [55, 51] [54, 55] NoOrders.members NoOrders.encode NoOrders.within NoOrders.decode NoOrders.decode_encode NoOrders.led record.noOrders tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  simp only [NewOrderList.decode, auctionType, nWTOrdType, nWTPrice, brokerPCT, noOrders, some_bind] <;> rfl

theorem NewOrderList.taken (record : NewOrderList) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [57, 51, 55, 51] record.auctionType (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 49] record.nWTOrdType (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 50] record.nWTPrice (by decide) (by decide))
     (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 52] record.brokerPCT (by decide) (by decide))
      (paired_cons pairing _ _ (paired_group pairing [55, 51] NoOrders.members NoOrders.encode NoOrders.within (by decide) (by decide) NoOrders.taken record.noOrders)
       (paired_none pairing)))))

structure NewOrderSingle where
  clOrdID : Terminated 1  -- tag 11
  handlInst : Option (Terminated 1)  -- tag 21
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  clientID : Option (Terminated 1)  -- tag 109
  execBroker : Option (Terminated 1)  -- tag 76
  account : Option (Terminated 1)  -- tag 1
  execInst : Option (Terminated 1)  -- tag 18
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  timeInForce : Option (Terminated 1)  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  text : Option (Terminated 1)  -- tag 58
  expireTime : Option (Terminated 1)  -- tag 126
  openClose : Terminated 1  -- tag 77
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  clearingAccount : Option (Terminated 1)  -- tag 440
  securityExchange : Option (Terminated 1)  -- tag 207
  clearingFirm : Option (Terminated 1)  -- tag 439
  allocAccount : Option (Terminated 1)  -- tag 79
  auctionType : Option (Terminated 1)  -- tag 9373
  auctionID : Option (Terminated 1)  -- tag 9370
  exposureFlag : Option (Terminated 1)  -- tag 9203
  nWTOrdType : Option (Terminated 1)  -- tag 9371
  nWTPrice : Option (Terminated 1)  -- tag 9372
  brokerPCT : Option (Terminated 1)  -- tag 9204
  rFPID : Option (Terminated 1)  -- tag 9210
  rFPInstr : Option (Terminated 1)  -- tag 9211

def NewOrderSingle.parts (record : NewOrderSingle) : List Part :=
  [Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49] record.handlInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [55, 54] record.execBroker,
   Part.optional [49] record.account,
   Part.optional [49, 56] record.execInst,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [53, 56] record.text,
   Part.optional [49, 50, 54] record.expireTime,
   Part.required [55, 55] record.openClose,
   Part.optional [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [52, 52, 48] record.clearingAccount,
   Part.optional [50, 48, 55] record.securityExchange,
   Part.optional [52, 51, 57] record.clearingFirm,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [57, 51, 55, 51] record.auctionType,
   Part.optional [57, 51, 55, 48] record.auctionID,
   Part.optional [57, 50, 48, 51] record.exposureFlag,
   Part.optional [57, 51, 55, 49] record.nWTOrdType,
   Part.optional [57, 51, 55, 50] record.nWTPrice,
   Part.optional [57, 50, 48, 52] record.brokerPCT,
   Part.optional [57, 50, 49, 48] record.rFPID,
   Part.optional [57, 50, 49, 49] record.rFPInstr]

def NewOrderSingle.tags : List (List (List UInt8)) :=
  [[[49, 49]], [[50, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[49, 48, 57]], [[55, 54]], [[49]], [[49, 56]], [[49, 49, 48]], [[49, 49, 49]], [[53, 57]], [[52, 55]], [[53, 56]], [[49, 50, 54]], [[55, 55]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[52, 52, 48]], [[50, 48, 55]], [[52, 51, 57]], [[55, 57]], [[57, 51, 55, 51]], [[57, 51, 55, 48]], [[57, 50, 48, 51]], [[57, 51, 55, 49]], [[57, 51, 55, 50]], [[57, 50, 48, 52]], [[57, 50, 49, 48]], [[57, 50, 49, 49]]]

theorem NewOrderSingle.shape (record : NewOrderSingle) : record.parts.map Part.tags = NewOrderSingle.tags := rfl

def NewOrderSingle.decode (tokens : List Token) : Option NewOrderSingle := do
  let clOrdID ← readRequired [49, 49] tokens
  let handlInst ← readOptional [50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let execBroker ← readOptional [55, 54] tokens
  let account ← readOptional [49] tokens
  let execInst ← readOptional [49, 56] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let text ← readOptional [53, 56] tokens
  let expireTime ← readOptional [49, 50, 54] tokens
  let openClose ← readRequired [55, 55] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let clearingAccount ← readOptional [52, 52, 48] tokens
  let securityExchange ← readOptional [50, 48, 55] tokens
  let clearingFirm ← readOptional [52, 51, 57] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let auctionType ← readOptional [57, 51, 55, 51] tokens
  let auctionID ← readOptional [57, 51, 55, 48] tokens
  let exposureFlag ← readOptional [57, 50, 48, 51] tokens
  let nWTOrdType ← readOptional [57, 51, 55, 49] tokens
  let nWTPrice ← readOptional [57, 51, 55, 50] tokens
  let brokerPCT ← readOptional [57, 50, 48, 52] tokens
  let rFPID ← readOptional [57, 50, 49, 48] tokens
  let rFPInstr ← readOptional [57, 50, 49, 49] tokens
  pure { clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, execBroker, account, execInst, minQty, maxFloor, timeInForce, rule80A, text, expireTime, openClose, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, clearingAccount, securityExchange, clearingFirm, allocAccount, auctionType, auctionID, exposureFlag, nWTOrdType, nWTPrice, brokerPCT, rFPID, rFPInstr }

theorem NewOrderSingle.decode_agrees (record : NewOrderSingle) (tokens : List Token)
    (agrees : ∀ tags ∈ NewOrderSingle.tags, select tags tokens = select tags (encodeParts record.parts)) :
    NewOrderSingle.decode tokens = some record := by
  have distinct : NewOrderSingle.tags.flatten.Nodup := by decide +kernel
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have execBroker := readOptional_part [55, 54] record.execBroker tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have text := readOptional_part [53, 56] record.text tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have expireTime := readOptional_part [49, 50, 54] record.expireTime tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have openClose := readRequired_part [55, 55] record.openClose tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have clearingAccount := readOptional_part [52, 52, 48] record.clearingAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  have securityExchange := readOptional_part [50, 48, 55] record.securityExchange tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 25 (by decide +kernel)))
  have clearingFirm := readOptional_part [52, 51, 57] record.clearingFirm tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 26 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 27 (by decide +kernel)))
  have auctionType := readOptional_part [57, 51, 55, 51] record.auctionType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 28 (by decide +kernel)))
  have auctionID := readOptional_part [57, 51, 55, 48] record.auctionID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 29 (by decide +kernel)))
  have exposureFlag := readOptional_part [57, 50, 48, 51] record.exposureFlag tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 30 (by decide +kernel)))
  have nWTOrdType := readOptional_part [57, 51, 55, 49] record.nWTOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 31 (by decide +kernel)))
  have nWTPrice := readOptional_part [57, 51, 55, 50] record.nWTPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 32 (by decide +kernel)))
  have brokerPCT := readOptional_part [57, 50, 48, 52] record.brokerPCT tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 33 (by decide +kernel)))
  have rFPID := readOptional_part [57, 50, 49, 48] record.rFPID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 34 (by decide +kernel)))
  have rFPInstr := readOptional_part [57, 50, 49, 49] record.rFPInstr tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 35 (by decide +kernel)))
  simp only [NewOrderSingle.decode, clOrdID, handlInst, symbol, side, orderQty, ordType, price, clientID, execBroker, account, execInst, minQty, maxFloor, timeInForce, rule80A, text, expireTime, openClose, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, clearingAccount, securityExchange, clearingFirm, allocAccount, auctionType, auctionID, exposureFlag, nWTOrdType, nWTPrice, brokerPCT, rFPID, rFPInstr, some_bind] <;> rfl

theorem NewOrderSingle.taken (record : NewOrderSingle) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_optional pairing [50, 49] record.handlInst (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [55, 54] record.execBroker (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [53, 56] record.text (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 50, 54] record.expireTime (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [55, 55] record.openClose (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [52, 52, 48] record.clearingAccount (by decide) (by decide))
                           (paired_cons pairing _ _ (paired_optional pairing [50, 48, 55] record.securityExchange (by decide) (by decide))
                            (paired_cons pairing _ _ (paired_optional pairing [52, 51, 57] record.clearingFirm (by decide) (by decide))
                             (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
                              (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 51] record.auctionType (by decide) (by decide))
                               (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 48] record.auctionID (by decide) (by decide))
                                (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 51] record.exposureFlag (by decide) (by decide))
                                 (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 49] record.nWTOrdType (by decide) (by decide))
                                  (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 50] record.nWTPrice (by decide) (by decide))
                                   (paired_cons pairing _ _ (paired_optional pairing [57, 50, 48, 52] record.brokerPCT (by decide) (by decide))
                                    (paired_cons pairing _ _ (paired_optional pairing [57, 50, 49, 48] record.rFPID (by decide) (by decide))
                                     (paired_cons pairing _ _ (paired_optional pairing [57, 50, 49, 49] record.rFPInstr (by decide) (by decide))
                                      (paired_none pairing))))))))))))))))))))))))))))))))))))

structure OrderCancelReplaceRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  handlInst : Option (Terminated 1)  -- tag 21
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  ordType : Terminated 1  -- tag 40
  price : Option (Terminated 1)  -- tag 44
  orderID : Option (Terminated 1)  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  execInst : Option (Terminated 1)  -- tag 18
  timeInForce : Option (Terminated 1)  -- tag 59
  rule80A : Option (Terminated 1)  -- tag 47
  account : Option (Terminated 1)  -- tag 1
  minQty : Option (Terminated 1)  -- tag 110
  maxFloor : Option (Terminated 1)  -- tag 111
  securityType : Option (Terminated 1)  -- tag 167
  maturityMonthYear : Terminated 1  -- tag 200
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202
  allocAccount : Option (Terminated 1)  -- tag 79
  nWTOrdType : Option (Terminated 1)  -- tag 9371
  nWTPrice : Option (Terminated 1)  -- tag 9372

def OrderCancelReplaceRequest.parts (record : OrderCancelReplaceRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.optional [50, 49] record.handlInst,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.required [52, 48] record.ordType,
   Part.optional [52, 52] record.price,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.optional [49, 56] record.execInst,
   Part.optional [53, 57] record.timeInForce,
   Part.optional [52, 55] record.rule80A,
   Part.optional [49] record.account,
   Part.optional [49, 49, 48] record.minQty,
   Part.optional [49, 49, 49] record.maxFloor,
   Part.optional [49, 54, 55] record.securityType,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice,
   Part.optional [55, 57] record.allocAccount,
   Part.optional [57, 51, 55, 49] record.nWTOrdType,
   Part.optional [57, 51, 55, 50] record.nWTPrice]

def OrderCancelReplaceRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [[50, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[52, 48]], [[52, 52]], [[51, 55]], [[49, 48, 57]], [[49, 56]], [[53, 57]], [[52, 55]], [[49]], [[49, 49, 48]], [[49, 49, 49]], [[49, 54, 55]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]], [[55, 57]], [[57, 51, 55, 49]], [[57, 51, 55, 50]]]

theorem OrderCancelReplaceRequest.shape (record : OrderCancelReplaceRequest) : record.parts.map Part.tags = OrderCancelReplaceRequest.tags := rfl

def OrderCancelReplaceRequest.decode (tokens : List Token) : Option OrderCancelReplaceRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let handlInst ← readOptional [50, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let ordType ← readRequired [52, 48] tokens
  let price ← readOptional [52, 52] tokens
  let orderID ← readOptional [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let execInst ← readOptional [49, 56] tokens
  let timeInForce ← readOptional [53, 57] tokens
  let rule80A ← readOptional [52, 55] tokens
  let account ← readOptional [49] tokens
  let minQty ← readOptional [49, 49, 48] tokens
  let maxFloor ← readOptional [49, 49, 49] tokens
  let securityType ← readOptional [49, 54, 55] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  let allocAccount ← readOptional [55, 57] tokens
  let nWTOrdType ← readOptional [57, 51, 55, 49] tokens
  let nWTPrice ← readOptional [57, 51, 55, 50] tokens
  pure { origClOrdID, clOrdID, handlInst, symbol, side, orderQty, ordType, price, orderID, clientID, execInst, timeInForce, rule80A, account, minQty, maxFloor, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, allocAccount, nWTOrdType, nWTPrice }

theorem OrderCancelReplaceRequest.decode_agrees (record : OrderCancelReplaceRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelReplaceRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelReplaceRequest.decode tokens = some record := by
  have distinct : OrderCancelReplaceRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have handlInst := readOptional_part [50, 49] record.handlInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have ordType := readRequired_part [52, 48] record.ordType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have price := readOptional_part [52, 52] record.price tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have execInst := readOptional_part [49, 56] record.execInst tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have timeInForce := readOptional_part [53, 57] record.timeInForce tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  have rule80A := readOptional_part [52, 55] record.rule80A tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 12 (by decide +kernel)))
  have account := readOptional_part [49] record.account tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 13 (by decide +kernel)))
  have minQty := readOptional_part [49, 49, 48] record.minQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 14 (by decide +kernel)))
  have maxFloor := readOptional_part [49, 49, 49] record.maxFloor tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 15 (by decide +kernel)))
  have securityType := readOptional_part [49, 54, 55] record.securityType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 16 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 17 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 18 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 19 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 20 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 21 (by decide +kernel)))
  have allocAccount := readOptional_part [55, 57] record.allocAccount tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 22 (by decide +kernel)))
  have nWTOrdType := readOptional_part [57, 51, 55, 49] record.nWTOrdType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 23 (by decide +kernel)))
  have nWTPrice := readOptional_part [57, 51, 55, 50] record.nWTPrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 24 (by decide +kernel)))
  simp only [OrderCancelReplaceRequest.decode, origClOrdID, clOrdID, handlInst, symbol, side, orderQty, ordType, price, orderID, clientID, execInst, timeInForce, rule80A, account, minQty, maxFloor, securityType, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, allocAccount, nWTOrdType, nWTPrice, some_bind] <;> rfl

theorem OrderCancelReplaceRequest.taken (record : OrderCancelReplaceRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_optional pairing [50, 49] record.handlInst (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
       (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
        (paired_cons pairing _ _ (paired_required pairing [52, 48] record.ordType (by decide) (by decide))
         (paired_cons pairing _ _ (paired_optional pairing [52, 52] record.price (by decide) (by decide))
          (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
           (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
            (paired_cons pairing _ _ (paired_optional pairing [49, 56] record.execInst (by decide) (by decide))
             (paired_cons pairing _ _ (paired_optional pairing [53, 57] record.timeInForce (by decide) (by decide))
              (paired_cons pairing _ _ (paired_optional pairing [52, 55] record.rule80A (by decide) (by decide))
               (paired_cons pairing _ _ (paired_optional pairing [49] record.account (by decide) (by decide))
                (paired_cons pairing _ _ (paired_optional pairing [49, 49, 48] record.minQty (by decide) (by decide))
                 (paired_cons pairing _ _ (paired_optional pairing [49, 49, 49] record.maxFloor (by decide) (by decide))
                  (paired_cons pairing _ _ (paired_optional pairing [49, 54, 55] record.securityType (by decide) (by decide))
                   (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
                    (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
                     (paired_cons pairing _ _ (paired_required pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
                      (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
                       (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
                        (paired_cons pairing _ _ (paired_optional pairing [55, 57] record.allocAccount (by decide) (by decide))
                         (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 49] record.nWTOrdType (by decide) (by decide))
                          (paired_cons pairing _ _ (paired_optional pairing [57, 51, 55, 50] record.nWTPrice (by decide) (by decide))
                           (paired_none pairing)))))))))))))))))))))))))

structure OrderCancelRequest where
  origClOrdID : Terminated 1  -- tag 41
  clOrdID : Terminated 1  -- tag 11
  symbol : Terminated 1  -- tag 55
  side : Terminated 1  -- tag 54
  orderQty : Terminated 1  -- tag 38
  orderID : Option (Terminated 1)  -- tag 37
  clientID : Option (Terminated 1)  -- tag 109
  maturityMonthYear : Terminated 1  -- tag 200
  maturityDay : Terminated 1  -- tag 205
  maturityDate : Terminated 1  -- tag 541
  putOrCall : Terminated 1  -- tag 201
  strikePrice : Terminated 1  -- tag 202

def OrderCancelRequest.parts (record : OrderCancelRequest) : List Part :=
  [Part.required [52, 49] record.origClOrdID,
   Part.required [49, 49] record.clOrdID,
   Part.required [53, 53] record.symbol,
   Part.required [53, 52] record.side,
   Part.required [51, 56] record.orderQty,
   Part.optional [51, 55] record.orderID,
   Part.optional [49, 48, 57] record.clientID,
   Part.required [50, 48, 48] record.maturityMonthYear,
   Part.required [50, 48, 53] record.maturityDay,
   Part.required [53, 52, 49] record.maturityDate,
   Part.required [50, 48, 49] record.putOrCall,
   Part.required [50, 48, 50] record.strikePrice]

def OrderCancelRequest.tags : List (List (List UInt8)) :=
  [[[52, 49]], [[49, 49]], [[53, 53]], [[53, 52]], [[51, 56]], [[51, 55]], [[49, 48, 57]], [[50, 48, 48]], [[50, 48, 53]], [[53, 52, 49]], [[50, 48, 49]], [[50, 48, 50]]]

theorem OrderCancelRequest.shape (record : OrderCancelRequest) : record.parts.map Part.tags = OrderCancelRequest.tags := rfl

def OrderCancelRequest.decode (tokens : List Token) : Option OrderCancelRequest := do
  let origClOrdID ← readRequired [52, 49] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let symbol ← readRequired [53, 53] tokens
  let side ← readRequired [53, 52] tokens
  let orderQty ← readRequired [51, 56] tokens
  let orderID ← readOptional [51, 55] tokens
  let clientID ← readOptional [49, 48, 57] tokens
  let maturityMonthYear ← readRequired [50, 48, 48] tokens
  let maturityDay ← readRequired [50, 48, 53] tokens
  let maturityDate ← readRequired [53, 52, 49] tokens
  let putOrCall ← readRequired [50, 48, 49] tokens
  let strikePrice ← readRequired [50, 48, 50] tokens
  pure { origClOrdID, clOrdID, symbol, side, orderQty, orderID, clientID, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice }

theorem OrderCancelRequest.decode_agrees (record : OrderCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderCancelRequest.decode tokens = some record := by
  have distinct : OrderCancelRequest.tags.flatten.Nodup := by decide +kernel
  have origClOrdID := readRequired_part [52, 49] record.origClOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have symbol := readRequired_part [53, 53] record.symbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have side := readRequired_part [53, 52] record.side tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  have orderQty := readRequired_part [51, 56] record.orderQty tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 4 (by decide +kernel)))
  have orderID := readOptional_part [51, 55] record.orderID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 5 (by decide +kernel)))
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 6 (by decide +kernel)))
  have maturityMonthYear := readRequired_part [50, 48, 48] record.maturityMonthYear tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 7 (by decide +kernel)))
  have maturityDay := readRequired_part [50, 48, 53] record.maturityDay tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 8 (by decide +kernel)))
  have maturityDate := readRequired_part [53, 52, 49] record.maturityDate tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 9 (by decide +kernel)))
  have putOrCall := readRequired_part [50, 48, 49] record.putOrCall tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 10 (by decide +kernel)))
  have strikePrice := readRequired_part [50, 48, 50] record.strikePrice tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 11 (by decide +kernel)))
  simp only [OrderCancelRequest.decode, origClOrdID, clOrdID, symbol, side, orderQty, orderID, clientID, maturityMonthYear, maturityDay, maturityDate, putOrCall, strikePrice, some_bind] <;> rfl

theorem OrderCancelRequest.taken (record : OrderCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_required pairing [52, 49] record.origClOrdID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [53, 53] record.symbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 52] record.side (by decide) (by decide))
      (paired_cons pairing _ _ (paired_required pairing [51, 56] record.orderQty (by decide) (by decide))
       (paired_cons pairing _ _ (paired_optional pairing [51, 55] record.orderID (by decide) (by decide))
        (paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
         (paired_cons pairing _ _ (paired_required pairing [50, 48, 48] record.maturityMonthYear (by decide) (by decide))
          (paired_cons pairing _ _ (paired_required pairing [50, 48, 53] record.maturityDay (by decide) (by decide))
           (paired_cons pairing _ _ (paired_required pairing [53, 52, 49] record.maturityDate (by decide) (by decide))
            (paired_cons pairing _ _ (paired_required pairing [50, 48, 49] record.putOrCall (by decide) (by decide))
             (paired_cons pairing _ _ (paired_required pairing [50, 48, 50] record.strikePrice (by decide) (by decide))
              (paired_none pairing))))))))))))

structure OrderMassCancelRequest where
  clientID : Option (Terminated 1)  -- tag 109
  clOrdID : Terminated 1  -- tag 11
  underlyingSymbol : Terminated 1  -- tag 311
  requestType : Terminated 1  -- tag 530

def OrderMassCancelRequest.parts (record : OrderMassCancelRequest) : List Part :=
  [Part.optional [49, 48, 57] record.clientID,
   Part.required [49, 49] record.clOrdID,
   Part.required [51, 49, 49] record.underlyingSymbol,
   Part.required [53, 51, 48] record.requestType]

def OrderMassCancelRequest.tags : List (List (List UInt8)) :=
  [[[49, 48, 57]], [[49, 49]], [[51, 49, 49]], [[53, 51, 48]]]

theorem OrderMassCancelRequest.shape (record : OrderMassCancelRequest) : record.parts.map Part.tags = OrderMassCancelRequest.tags := rfl

def OrderMassCancelRequest.decode (tokens : List Token) : Option OrderMassCancelRequest := do
  let clientID ← readOptional [49, 48, 57] tokens
  let clOrdID ← readRequired [49, 49] tokens
  let underlyingSymbol ← readRequired [51, 49, 49] tokens
  let requestType ← readRequired [53, 51, 48] tokens
  pure { clientID, clOrdID, underlyingSymbol, requestType }

theorem OrderMassCancelRequest.decode_agrees (record : OrderMassCancelRequest) (tokens : List Token)
    (agrees : ∀ tags ∈ OrderMassCancelRequest.tags, select tags tokens = select tags (encodeParts record.parts)) :
    OrderMassCancelRequest.decode tokens = some record := by
  have distinct : OrderMassCancelRequest.tags.flatten.Nodup := by decide +kernel
  have clientID := readOptional_part [49, 48, 57] record.clientID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 0 (by decide +kernel)))
  have clOrdID := readRequired_part [49, 49] record.clOrdID tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 1 (by decide +kernel)))
  have underlyingSymbol := readRequired_part [51, 49, 49] record.underlyingSymbol tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 2 (by decide +kernel)))
  have requestType := readRequired_part [53, 51, 48] record.requestType tokens
    ((agrees _ (by decide +kernel)).trans (select_part _ _ record.shape distinct 3 (by decide +kernel)))
  simp only [OrderMassCancelRequest.decode, clientID, clOrdID, underlyingSymbol, requestType, some_bind] <;> rfl

theorem OrderMassCancelRequest.taken (record : OrderMassCancelRequest) : Paired pairing (encodeParts record.parts) :=
  paired_cons pairing _ _ (paired_optional pairing [49, 48, 57] record.clientID (by decide) (by decide))
   (paired_cons pairing _ _ (paired_required pairing [49, 49] record.clOrdID (by decide) (by decide))
    (paired_cons pairing _ _ (paired_required pairing [51, 49, 49] record.underlyingSymbol (by decide) (by decide))
     (paired_cons pairing _ _ (paired_required pairing [53, 51, 48] record.requestType (by decide) (by decide))
      (paired_none pairing))))

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
  | newOrderList (header : Header) (r0 : NewOrderList)
  | newOrderSingle (header : Header) (r0 : NewOrderSingle)
  | orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest)
  | orderCancelRequest (header : Header) (r0 : OrderCancelRequest)
  | orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest)
  | reject (header : Header) (r0 : Reject)
  | resendRequest (header : Header) (r0 : ResendRequest)
  | sequenceReset (header : Header) (r0 : SequenceReset)
  | testRequest (header : Header) (r0 : TestRequest)

def Message.tokens : Message → List Token
  | .heartbeat header r0 => ⟨[51, 53], [48]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logon header r0 => ⟨[51, 53], [65]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .logout header r0 => ⟨[51, 53], [53]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderList header r0 => ⟨[51, 53], [69]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .newOrderSingle header r0 => ⟨[51, 53], [68]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelReplaceRequest header r0 => ⟨[51, 53], [71]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderCancelRequest header r0 => ⟨[51, 53], [70]⟩ :: encodeParts (header.parts ++ r0.parts)
  | .orderMassCancelRequest header r0 => ⟨[51, 53], [113]⟩ :: encodeParts (header.parts ++ r0.parts)
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
      else if token.value = [69] then
        if known (Header.tags ++ NewOrderList.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderList.decode rest
          pure (.newOrderList header r0)
        else none
      else if token.value = [68] then
        if known (Header.tags ++ NewOrderSingle.tags) rest then do
          let header ← Header.decode rest
          let r0 ← NewOrderSingle.decode rest
          pure (.newOrderSingle header r0)
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
      else if token.value = [113] then
        if known (Header.tags ++ OrderMassCancelRequest.tags) rest then do
          let header ← Header.decode rest
          let r0 ← OrderMassCancelRequest.decode rest
          pure (.orderMassCancelRequest header r0)
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

theorem Message.decode_newOrderList (header : Header) (r0 : NewOrderList) :
    Message.decode (Message.tokens (.newOrderList header r0)) = some (.newOrderList header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderList.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderList.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderList.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderList.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decode (Message.tokens (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) rfl rfl (by decide +kernel))
  have c1 := NewOrderSingle.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (NewOrderSingle.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ NewOrderSingle.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelReplaceRequest (header : Header) (r0 : OrderCancelReplaceRequest) :
    Message.decode (Message.tokens (.orderCancelReplaceRequest header r0)) = some (.orderCancelReplaceRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelReplaceRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelReplaceRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelReplaceRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderCancelRequest (header : Header) (r0 : OrderCancelRequest) :
    Message.decode (Message.tokens (.orderCancelRequest header r0)) = some (.orderCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderCancelRequest.tags) rfl
  simp only [List.nil_append, List.append_nil] at c0 c1 knows
  simp +decide only [Message.tokens, Message.decode, knows, c0, c1, ite_true, ite_false, some_bind] <;> rfl

theorem Message.decode_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decode (Message.tokens (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have c0 := Header.decode_agrees header _ (agrees_slice ([]) (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) rfl rfl (by decide +kernel))
  have c1 := OrderMassCancelRequest.decode_agrees r0 _ (agrees_slice (header.parts) (r0.parts) ([]) (Header.tags) (OrderMassCancelRequest.tags) ([]) rfl rfl (by decide +kernel))
  have knows := known_parts (header.parts ++ r0.parts) (Header.tags ++ OrderMassCancelRequest.tags) rfl
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

theorem Message.decode_tokens (message : Message) : Message.decode message.tokens = some message := by
  cases message with
  | heartbeat header r0 => exact Message.decode_heartbeat header r0
  | logon header r0 => exact Message.decode_logon header r0
  | logout header r0 => exact Message.decode_logout header r0
  | newOrderList header r0 => exact Message.decode_newOrderList header r0
  | newOrderSingle header r0 => exact Message.decode_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decode_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decode_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decode_orderMassCancelRequest header r0
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

theorem Message.decodeBytes_newOrderList (header : Header) (r0 : NewOrderList) :
    Message.decodeBytes (Message.encode (.newOrderList header r0)) = some (.newOrderList header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [69]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderList.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderList header r0

theorem Message.decodeBytes_newOrderSingle (header : Header) (r0 : NewOrderSingle) :
    Message.decodeBytes (Message.encode (.newOrderSingle header r0)) = some (.newOrderSingle header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [68]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (NewOrderSingle.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_newOrderSingle header r0

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

theorem Message.decodeBytes_orderMassCancelRequest (header : Header) (r0 : OrderMassCancelRequest) :
    Message.decodeBytes (Message.encode (.orderMassCancelRequest header r0)) = some (.orderMassCancelRequest header r0) := by
  have tokens := decodeTokens_message pairing ⟨[51, 53], [113]⟩ (header.parts ++ r0.parts)
    (by decide) (by decide) (by decide) (paired_parts pairing (header.parts) (r0.parts) (Header.taken header) (OrderMassCancelRequest.taken r0))
  simp only [Message.decodeBytes, Message.encode, Message.tokens] at tokens ⊢
  rw [tokens, some_bind]
  exact Message.decode_orderMassCancelRequest header r0

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
  | newOrderList header r0 => exact Message.decodeBytes_newOrderList header r0
  | newOrderSingle header r0 => exact Message.decodeBytes_newOrderSingle header r0
  | orderCancelReplaceRequest header r0 => exact Message.decodeBytes_orderCancelReplaceRequest header r0
  | orderCancelRequest header r0 => exact Message.decodeBytes_orderCancelRequest header r0
  | orderMassCancelRequest header r0 => exact Message.decodeBytes_orderMassCancelRequest header r0
  | reject header r0 => exact Message.decodeBytes_reject header r0
  | resendRequest header r0 => exact Message.decodeBytes_resendRequest header r0
  | sequenceReset header r0 => exact Message.decodeBytes_sequenceReset header r0
  | testRequest header r0 => exact Message.decodeBytes_testRequest header r0

/-- BeginString as the venue states it: one of FIX.4.0, FIX.4.1, FIX.4.2, read with the message -/
def begins : List (List UInt8) := [[70, 73, 88, 46, 52, 46, 48], [70, 73, 88, 46, 52, 46, 49], [70, 73, 88, 46, 52, 46, 50]]

/-- A packet: the BeginString it was sent under, and the message -/
abbrev Packet := Terminated 1 × Message

def Packet.encode (packet : Packet) : List UInt8 := encodeFixAmong Message.encode packet

def Packet.decode (bytes : List UInt8) : Option (Packet × List UInt8) := decodeFixAmong begins Message.decodeBytes bytes

theorem Packet.decode_encode (packet : Packet) (stated : packet.1.val ∈ begins) (rest : List UInt8) :
    Packet.decode (Packet.encode packet ++ rest) = some (packet, rest) :=
  decodeFixAmong_encodeFixAmong begins Message.encode Message.decodeBytes Message.decodeBytes_encode packet stated rest

end Omi.NasdaqNtxoptionsOrderentryFixV20FClient
