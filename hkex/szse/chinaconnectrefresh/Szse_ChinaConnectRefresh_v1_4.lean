import Wire

/-!
# Hong Kong Exchanges and Clearing Orion Market Data China Connect Refresh v1.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.HkexSzseChinaconnectrefreshOmdV14

/-- Shortsell Flag: one byte code -/
def ShortsellFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ShortsellFlag where
  | shortSellAllowed -- Short Sell Allowed
  | shortSellNotAllowed -- Short Sell Not Allowed
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortsellFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortsellFlag

def toByte : ShortsellFlag → UInt8
  | .shortSellAllowed => 0x59
  | .shortSellNotAllowed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortsellFlag :=
  if byte = 0x59 then .shortSellAllowed
  else .shortSellNotAllowed

def ofByte (byte : UInt8) : ShortsellFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortsellFlag) : ofByte value.toByte = value := by
  cases value with
  | shortSellAllowed => decide
  | shortSellNotAllowed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortsellFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortsellFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortsellFlag) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortsellFlag) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortsellFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortsellFlag

/-- Market Definition Message: 36 bytes -/
structure MarketDefinitionMessage where
  marketCode : Alpha 4
  marketName : Alpha 25
  currencyCode : Alpha 3
  numberOfSecurities : BitVec 32
  deriving DecidableEq, Repr

namespace MarketDefinitionMessage

def encode (message : MarketDefinitionMessage) : List UInt8 :=
  Alpha.encode message.marketCode
    ++ (Alpha.encode message.marketName
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 4 message.numberOfSecurities)))

def decode (bytes : List UInt8) : Option (MarketDefinitionMessage × List UInt8) := do
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (marketName, bytes) ← Alpha.decode 25 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (numberOfSecurities, bytes) ← decodeUIntLE 4 bytes
  pure ({ marketCode, marketName, currencyCode, numberOfSecurities }, bytes)

@[simp] theorem encode_length (message : MarketDefinitionMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDefinitionMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Security Definition Message: 216 bytes -/
structure SecurityDefinitionMessage where
  securityCode : BitVec 32
  marketCode : Alpha 4
  isinCode : Alpha 12
  instrumentType : Alpha 4
  filler2 : Alpha 2
  securityShortName : Alpha 40
  currencyCode : Alpha 3
  filler60 : Alpha 60
  securityNameGb : Alpha 60
  lotSize : BitVec 32
  previousClosingPrice : BitVec 32
  filler1 : Alpha 1
  shortsellFlag : ShortsellFlag
  filler6 : Alpha 6
  listingDate : BitVec 32
  filler7 : Alpha 7
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (Alpha.encode message.marketCode
    ++ (Alpha.encode message.isinCode
    ++ (Alpha.encode message.instrumentType
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.securityShortName
    ++ (Alpha.encode message.currencyCode
    ++ (Alpha.encode message.filler60
    ++ (Alpha.encode message.securityNameGb
    ++ (encodeUIntLE 4 message.lotSize
    ++ (encodeUIntLE 4 message.previousClosingPrice
    ++ (Alpha.encode message.filler1
    ++ (ShortsellFlag.encode message.shortsellFlag
    ++ (Alpha.encode message.filler6
    ++ (encodeUIntLE 4 message.listingDate
    ++ (Alpha.encode message.filler7)))))))))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (marketCode, bytes) ← Alpha.decode 4 bytes
  let (isinCode, bytes) ← Alpha.decode 12 bytes
  let (instrumentType, bytes) ← Alpha.decode 4 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (securityShortName, bytes) ← Alpha.decode 40 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (filler60, bytes) ← Alpha.decode 60 bytes
  let (securityNameGb, bytes) ← Alpha.decode 60 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (previousClosingPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (shortsellFlag, bytes) ← ShortsellFlag.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (listingDate, bytes) ← decodeUIntLE 4 bytes
  let (filler7, bytes) ← Alpha.decode 7 bytes
  pure ({ securityCode, marketCode, isinCode, instrumentType, filler2, securityShortName, currencyCode, filler60, securityNameGb, lotSize, previousClosingPrice, filler1, shortsellFlag, filler6, listingDate, filler7 }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessage) : (encode message).length = 216 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ShortsellFlag.encode_length]

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShortsellFlag.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Security Status Message: 16 bytes -/
structure SecurityStatusMessage where
  securityCode : BitVec 32
  securityTradingStatus : BitVec 8
  filler3 : Alpha 3
  tradingPhaseCode : Alpha 8
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (Alpha.encode message.filler3
    ++ (Alpha.encode message.tradingPhaseCode)))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (filler3, bytes) ← Alpha.decode 3 bytes
  let (tradingPhaseCode, bytes) ← Alpha.decode 8 bytes
  pure ({ securityCode, securityTradingStatus, filler3, tradingPhaseCode }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusMessage

/-- Statistics Message: 48 bytes -/
structure StatisticsMessage where
  securityCode : BitVec 32
  sharesTraded : BitVec 64
  turnover : BitVec 64
  highPrice : BitVec 32
  lowPrice : BitVec 32
  lastPrice : BitVec 32
  openingPrice : BitVec 32
  filler12 : Alpha 12
  deriving DecidableEq, Repr

namespace StatisticsMessage

def encode (message : StatisticsMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.sharesTraded
    ++ (encodeUIntLE 8 message.turnover
    ++ (encodeUIntLE 4 message.highPrice
    ++ (encodeUIntLE 4 message.lowPrice
    ++ (encodeUIntLE 4 message.lastPrice
    ++ (encodeUIntLE 4 message.openingPrice
    ++ (Alpha.encode message.filler12)))))))

def decode (bytes : List UInt8) : Option (StatisticsMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (sharesTraded, bytes) ← decodeUIntLE 8 bytes
  let (turnover, bytes) ← decodeUIntLE 8 bytes
  let (highPrice, bytes) ← decodeUIntLE 4 bytes
  let (lowPrice, bytes) ← decodeUIntLE 4 bytes
  let (lastPrice, bytes) ← decodeUIntLE 4 bytes
  let (openingPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler12, bytes) ← Alpha.decode 12 bytes
  pure ({ securityCode, sharesTraded, turnover, highPrice, lowPrice, lastPrice, openingPrice, filler12 }, bytes)

@[simp] theorem encode_length (message : StatisticsMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StatisticsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StatisticsMessage

/-- Top Of Book Message: 36 bytes -/
structure TopOfBookMessage where
  securityCode : BitVec 32
  aggregateBidQuantity : BitVec 64
  aggregateAskQuantity : BitVec 64
  bidPrice : BitVec 32
  askPrice : BitVec 32
  filler8 : Alpha 8
  deriving DecidableEq, Repr

namespace TopOfBookMessage

def encode (message : TopOfBookMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityCode
    ++ (encodeUIntLE 8 message.aggregateBidQuantity
    ++ (encodeUIntLE 8 message.aggregateAskQuantity
    ++ (encodeUIntLE 4 message.bidPrice
    ++ (encodeUIntLE 4 message.askPrice
    ++ (Alpha.encode message.filler8)))))

def decode (bytes : List UInt8) : Option (TopOfBookMessage × List UInt8) := do
  let (securityCode, bytes) ← decodeUIntLE 4 bytes
  let (aggregateBidQuantity, bytes) ← decodeUIntLE 8 bytes
  let (aggregateAskQuantity, bytes) ← decodeUIntLE 8 bytes
  let (bidPrice, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 4 bytes
  let (filler8, bytes) ← Alpha.decode 8 bytes
  pure ({ securityCode, aggregateBidQuantity, aggregateAskQuantity, bidPrice, askPrice, filler8 }, bytes)

@[simp] theorem encode_length (message : TopOfBookMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TopOfBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TopOfBookMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | marketDefinitionMessage (message : MarketDefinitionMessage) -- 610
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 611
  | securityStatusMessage (message : SecurityStatusMessage) -- 621
  | statisticsMessage (message : StatisticsMessage) -- 660
  | topOfBookMessage (message : TopOfBookMessage) -- 655
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .marketDefinitionMessage _ => 610
  | .refreshCompleteMessage _ => 203
  | .securityDefinitionMessage _ => 611
  | .securityStatusMessage _ => 621
  | .statisticsMessage _ => 660
  | .topOfBookMessage _ => 655

def encode : Payload → List UInt8
  | .marketDefinitionMessage message => MarketDefinitionMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .statisticsMessage message => StatisticsMessage.encode message
  | .topOfBookMessage message => TopOfBookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 216 := by
  cases message with
  | marketDefinitionMessage inner =>
    simp only [encode, MarketDefinitionMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [encode, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [encode, StatisticsMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [encode, TopOfBookMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 610 then (MarketDefinitionMessage.decode bytes).map fun (message, rest) => (.marketDefinitionMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else if tag = 611 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 621 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 660 then (StatisticsMessage.decode bytes).map fun (message, rest) => (.statisticsMessage message, rest)
  else if tag = 655 then (TopOfBookMessage.decode bytes).map fun (message, rest) => (.topOfBookMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | marketDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, MarketDefinitionMessage.encode_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | statisticsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, StatisticsMessage.encode_length]
    omega
  | topOfBookMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TopOfBookMessage.encode_length]
    omega

/-- Size rule: Msg Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.HkexSzseChinaconnectrefreshOmdV14
