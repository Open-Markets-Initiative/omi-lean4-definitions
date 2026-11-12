import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 35 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct35IntraV11

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive EventCode where
  | startOfSystemHours -- Start Of System Hours
  | cancelationOfOffers -- Cancelation Of Offers
  | startOfOpeningAuction -- Start Of Opening Auction
  | startOfContinuousMarket -- Start Of Continuous Market
  | startOfWapPeriod -- Start Of Wap Period
  | continuousMarketEnds -- Continuous Market Ends
  | startOfAfterClosingPhase -- Start Of After Closing Phase
  | itEndsAfterClosing -- It Ends After Closing
  | transmissionOfFinalPricesEnds -- Transmission Of Final Prices Ends
  | endOfSystemHours -- End Of System Hours
  | startOfAdministrativeRecess -- Start Of Administrative Recess
  | endOfAdministrativeRecess -- End Of Administrative Recess
  | startDvmamxMarkets -- Start Dvmamx Markets
  | endOfDvmaMarkets -- End Of Dvma Markets
  | endOfMxMarkets -- End Of Mx Markets
  | startOfOpcModality -- Start Of Opc Modality
  | endOfOpcModality -- End Of Opc Modality
  | startOfSettlementAuction -- Start Of Settlement Auction
  | endOfSettlementAuction -- End Of Settlement Auction
  | finalRegisterOfSettlementPrices -- Final Register Of Settlement Prices
  | openInterest -- Open Interest
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfSystemHours => 0x41
  | .cancelationOfOffers => 0x42
  | .startOfOpeningAuction => 0x43
  | .startOfContinuousMarket => 0x44
  | .startOfWapPeriod => 0x45
  | .continuousMarketEnds => 0x46
  | .startOfAfterClosingPhase => 0x47
  | .itEndsAfterClosing => 0x48
  | .transmissionOfFinalPricesEnds => 0x4A
  | .endOfSystemHours => 0x4B
  | .startOfAdministrativeRecess => 0x4D
  | .endOfAdministrativeRecess => 0x4E
  | .startDvmamxMarkets => 0x4F
  | .endOfDvmaMarkets => 0x50
  | .endOfMxMarkets => 0x51
  | .startOfOpcModality => 0x52
  | .endOfOpcModality => 0x53
  | .startOfSettlementAuction => 0x54
  | .endOfSettlementAuction => 0x55
  | .finalRegisterOfSettlementPrices => 0x56
  | .openInterest => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x41 then .startOfSystemHours
  else if byte = 0x42 then .cancelationOfOffers
  else if byte = 0x43 then .startOfOpeningAuction
  else if byte = 0x44 then .startOfContinuousMarket
  else if byte = 0x45 then .startOfWapPeriod
  else if byte = 0x46 then .continuousMarketEnds
  else if byte = 0x47 then .startOfAfterClosingPhase
  else if byte = 0x48 then .itEndsAfterClosing
  else if byte = 0x4A then .transmissionOfFinalPricesEnds
  else if byte = 0x4B then .endOfSystemHours
  else if byte = 0x4D then .startOfAdministrativeRecess
  else if byte = 0x4E then .endOfAdministrativeRecess
  else if byte = 0x4F then .startDvmamxMarkets
  else if byte = 0x50 then .endOfDvmaMarkets
  else if byte = 0x51 then .endOfMxMarkets
  else if byte = 0x52 then .startOfOpcModality
  else if byte = 0x53 then .endOfOpcModality
  else if byte = 0x54 then .startOfSettlementAuction
  else if byte = 0x55 then .endOfSettlementAuction
  else if byte = 0x56 then .finalRegisterOfSettlementPrices
  else .openInterest

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | cancelationOfOffers => decide
  | startOfOpeningAuction => decide
  | startOfContinuousMarket => decide
  | startOfWapPeriod => decide
  | continuousMarketEnds => decide
  | startOfAfterClosingPhase => decide
  | itEndsAfterClosing => decide
  | transmissionOfFinalPricesEnds => decide
  | endOfSystemHours => decide
  | startOfAdministrativeRecess => decide
  | endOfAdministrativeRecess => decide
  | startDvmamxMarkets => decide
  | endOfDvmaMarkets => decide
  | endOfMxMarkets => decide
  | startOfOpcModality => decide
  | endOfOpcModality => decide
  | startOfSettlementAuction => decide
  | endOfSettlementAuction => decide
  | finalRegisterOfSettlementPrices => decide
  | openInterest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x4C, 0x47, 0x44, 0x46, 0x45, 0x4D, 0x58, 0x56, 0x4A, 0x42, 0x54, 0x49, 0x57, 0x20]

inductive Market where
  | local_ -- Local
  | global -- Global
  | localDebt -- Local Debt
  | globalDebt -- Global Debt
  | money -- Money
  | dollarOptionMarket -- Dollar Option Market
  | stockMarket -- Stock Market
  | forexAndRatesMarket -- Forex And Rates Market
  | fixedIncome -- Fixed Income
  | variableIncome -- Variable Income
  | metals -- Metals
  | mutualFunds -- Mutual Funds
  | warrants -- Warrants
  | allMarkets -- All Markets
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .local_ => 0x4C
  | .global => 0x47
  | .localDebt => 0x44
  | .globalDebt => 0x46
  | .money => 0x45
  | .dollarOptionMarket => 0x4D
  | .stockMarket => 0x58
  | .forexAndRatesMarket => 0x56
  | .fixedIncome => 0x4A
  | .variableIncome => 0x42
  | .metals => 0x54
  | .mutualFunds => 0x49
  | .warrants => 0x57
  | .allMarkets => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x4C then .local_
  else if byte = 0x47 then .global
  else if byte = 0x44 then .localDebt
  else if byte = 0x46 then .globalDebt
  else if byte = 0x45 then .money
  else if byte = 0x4D then .dollarOptionMarket
  else if byte = 0x58 then .stockMarket
  else if byte = 0x56 then .forexAndRatesMarket
  else if byte = 0x4A then .fixedIncome
  else if byte = 0x42 then .variableIncome
  else if byte = 0x54 then .metals
  else if byte = 0x49 then .mutualFunds
  else if byte = 0x57 then .warrants
  else .allMarkets

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | global => decide
  | localDebt => decide
  | globalDebt => decide
  | money => decide
  | dollarOptionMarket => decide
  | stockMarket => decide
  | forexAndRatesMarket => decide
  | fixedIncome => decide
  | variableIncome => decide
  | metals => decide
  | mutualFunds => decide
  | warrants => decide
  | allMarkets => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Market) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Market × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Market) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Market) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Market) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Market

/-- Type: one byte code -/
def Type_.codes : List UInt8 :=
  [0x45, 0x53, 0x47]

inductive Type_ where
  | equity -- Equity
  | strategy -- Strategy
  | spbmvesg -- Spbmvesg
  | unlisted (byte : { byte : UInt8 // byte ∉ Type_.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Type_

def toByte : Type_ → UInt8
  | .equity => 0x45
  | .strategy => 0x53
  | .spbmvesg => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Type_ :=
  if byte = 0x45 then .equity
  else if byte = 0x53 then .strategy
  else .spbmvesg

def ofByte (byte : UInt8) : Type_ :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Type_) : ofByte value.toByte = value := by
  cases value with
  | equity => decide
  | strategy => decide
  | spbmvesg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Type_) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Type_ × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Type_) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Type_) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Type_) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Type_

/-- Events System Message: 22 bytes -/
structure EventsSystemMessage where
  instrumentNumber : BitVec 32
  eventCode : EventCode
  market : Market
  sendingTime : BitVec 64
  endingTime : BitVec 64
  deriving DecidableEq, Repr

namespace EventsSystemMessage

def encode (message : EventsSystemMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (EventCode.encode message.eventCode
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.endingTime))))

def decode (bytes : List UInt8) : Option (EventsSystemMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (market, bytes) ← Market.decode bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (endingTime, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, eventCode, market, sendingTime, endingTime }, bytes)

@[simp] theorem encode_length (message : EventsSystemMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length, Market.encode_length]

theorem encode_length_pos (message : EventsSystemMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventsSystemMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EventsSystemMessage

/-- Indices Components Message: 57 bytes -/
structure IndicesComponentsMessage where
  date : BitVec 64
  component : Alpha 2
  sector : BitVec 8
  type : Type_
  issuer : Alpha 7
  series : Alpha 6
  indicesStocks : BitVec 64
  lastPrice : BitVec 64
  closingPrice : BitVec 64
  influence : BitVec 64
  deriving DecidableEq, Repr

namespace IndicesComponentsMessage

def encode (message : IndicesComponentsMessage) : List UInt8 :=
  encodeUInt 8 message.date
    ++ (Alpha.encode message.component
    ++ (encodeUInt 1 message.sector
    ++ (Type_.encode message.type
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.indicesStocks
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.closingPrice
    ++ (encodeUInt 8 message.influence)))))))))

def decode (bytes : List UInt8) : Option (IndicesComponentsMessage × List UInt8) := do
  let (date, bytes) ← decodeUInt 8 bytes
  let (component, bytes) ← Alpha.decode 2 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (type, bytes) ← Type_.decode bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (indicesStocks, bytes) ← decodeUInt 8 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (closingPrice, bytes) ← decodeUInt 8 bytes
  let (influence, bytes) ← decodeUInt 8 bytes
  pure ({ date, component, sector, type, issuer, series, indicesStocks, lastPrice, closingPrice, influence }, bytes)

@[simp] theorem encode_length (message : IndicesComponentsMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Type_.encode_length]

theorem encode_length_pos (message : IndicesComponentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicesComponentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Type_.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndicesComponentsMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | eventsSystemMessage (message : EventsSystemMessage) -- 83
  | indicesComponentsMessage (message : IndicesComponentsMessage) -- 87
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .eventsSystemMessage _ => 83
  | .indicesComponentsMessage _ => 87

def encode : Payload → List UInt8
  | .eventsSystemMessage message => EventsSystemMessage.encode message
  | .indicesComponentsMessage message => IndicesComponentsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 57 := by
  cases message with
  | eventsSystemMessage inner =>
    simp only [encode, EventsSystemMessage.encode_length]
    omega
  | indicesComponentsMessage inner =>
    simp only [encode, IndicesComponentsMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (EventsSystemMessage.decode bytes).map fun (message, rest) => (.eventsSystemMessage message, rest)
  else if tag = 87 then (IndicesComponentsMessage.decode bytes).map fun (message, rest) => (.indicesComponentsMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Block -/
structure MessageBlock where
  payload : Payload
  deriving DecidableEq, Repr

namespace MessageBlock

def encodeBody (message : MessageBlock) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (MessageBlock × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : MessageBlock) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MessageBlock) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | eventsSystemMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EventsSystemMessage.encode_length]
    omega
  | indicesComponentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicesComponentsMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : MessageBlock → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (MessageBlock × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : MessageBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MessageBlock) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end MessageBlock

/-- Packet -/
structure Packet where
  length : BitVec 16
  marketDataGroup : BitVec 8
  session : BitVec 8
  sequenceNumber : BitVec 32
  datetime : BitVec 64
  messageBlock : Bounded 1 MessageBlock
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.length
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messageBlock.val.length)
    ++ (encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 8 message.datetime
    ++ (encodeMany MessageBlock.encode message.messageBlock.val))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (totalMessages, bytes) ← decodeUInt 1 bytes
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (datetime, bytes) ← decodeUInt 8 bytes
  let (messageBlock_, bytes) ← decodeMany MessageBlock.decode totalMessages.toNat bytes
  if fits_messageBlock : messageBlock_.length < 256 ^ 1 then
    pure ({ length, marketDataGroup, session, sequenceNumber, datetime, messageBlock := ⟨messageBlock_, fits_messageBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MessageBlock.encode MessageBlock.decode MessageBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messageBlock.length_lt]
  rfl

end Packet

end Omi.BmvBmvmarketdataProduct35IntraV11
