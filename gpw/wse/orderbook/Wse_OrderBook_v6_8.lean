import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Order Book v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwWseOrderbookXdpV68

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x35]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | sellShortEquivalentToValue2SellOptionalForExchangeMembersAndNotMonitoredByTheWse -- Sell Short Equivalent To Value 2 Sell Optional For Exchange Members And Not Monitored By The Wse
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .sellShortEquivalentToValue2SellOptionalForExchangeMembersAndNotMonitoredByTheWse => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else .sellShortEquivalentToValue2SellOptionalForExchangeMembersAndNotMonitoredByTheWse

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShortEquivalentToValue2SellOptionalForExchangeMembersAndNotMonitoredByTheWse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x31, 0x32, 0x4B, 0x50]

inductive OrderType where
  | marketOrder -- Market Order
  | limitOrder -- Limit Order
  | marketToLimitOrder -- Market To Limit Order
  | pegOrder -- Peg Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .marketOrder => 0x31
  | .limitOrder => 0x32
  | .marketToLimitOrder => 0x4B
  | .pegOrder => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x31 then .marketOrder
  else if byte = 0x32 then .limitOrder
  else if byte = 0x4B then .marketToLimitOrder
  else .pegOrder

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | marketOrder => decide
  | limitOrder => decide
  | marketToLimitOrder => decide
  | pegOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Action Type: one byte code -/
def ActionType.codes : List UInt8 :=
  [0x41, 0x4D, 0x44, 0x46, 0x59]

inductive ActionType where
  | newOrder -- New Order
  | modificationOfExistingOrderCaseOfPartialFill -- Modification Of Existing Order Case Of Partial Fill
  | deletionOfOrderIdentifiedByOrderId -- Deletion Of Order Identified By Order Id
  | deletionAllOrdersForOneInstrumentAtTheStartOfTheDayBeforeTheOrderBookRetransmission -- Deletion All Orders For One Instrument At The Start Of The Day Before The Order Book Retransmission
  | retransmissionOfAllOrdersForTheGivenInstrument -- Retransmission Of All Orders For The Given Instrument
  | unlisted (byte : { byte : UInt8 // byte ∉ ActionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ActionType

def toByte : ActionType → UInt8
  | .newOrder => 0x41
  | .modificationOfExistingOrderCaseOfPartialFill => 0x4D
  | .deletionOfOrderIdentifiedByOrderId => 0x44
  | .deletionAllOrdersForOneInstrumentAtTheStartOfTheDayBeforeTheOrderBookRetransmission => 0x46
  | .retransmissionOfAllOrdersForTheGivenInstrument => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ActionType :=
  if byte = 0x41 then .newOrder
  else if byte = 0x4D then .modificationOfExistingOrderCaseOfPartialFill
  else if byte = 0x44 then .deletionOfOrderIdentifiedByOrderId
  else if byte = 0x46 then .deletionAllOrdersForOneInstrumentAtTheStartOfTheDayBeforeTheOrderBookRetransmission
  else .retransmissionOfAllOrdersForTheGivenInstrument

def ofByte (byte : UInt8) : ActionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ActionType) : ofByte value.toByte = value := by
  cases value with
  | newOrder => decide
  | modificationOfExistingOrderCaseOfPartialFill => decide
  | deletionOfOrderIdentifiedByOrderId => decide
  | deletionAllOrdersForOneInstrumentAtTheStartOfTheDayBeforeTheOrderBookRetransmission => decide
  | retransmissionOfAllOrdersForTheGivenInstrument => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ActionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ActionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ActionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ActionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ActionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ActionType

/-- Retransmission Indicator: one byte code -/
def RetransmissionIndicator.codes : List UInt8 :=
  [0x42, 0x45]

inductive RetransmissionIndicator where
  | beginningOfTheRetransmission -- Beginning Of The Retransmission
  | endOfTheRetransmission -- End Of The Retransmission
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIndicator

def toByte : RetransmissionIndicator → UInt8
  | .beginningOfTheRetransmission => 0x42
  | .endOfTheRetransmission => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RetransmissionIndicator :=
  if byte = 0x42 then .beginningOfTheRetransmission
  else .endOfTheRetransmission

def ofByte (byte : UInt8) : RetransmissionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIndicator) : ofByte value.toByte = value := by
  cases value with
  | beginningOfTheRetransmission => decide
  | endOfTheRetransmission => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetransmissionIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetransmissionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIndicator

/-- Order Update Market Sheet Message: 60 bytes -/
structure OrderUpdateMarketSheetMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  price : BitVec 32
  aggregatedVolume : BitVec 32
  volume : BitVec 32
  linkId : BitVec 32
  orderId : BitVec 32
  systemId : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  numberOrders : BitVec 16
  side : Side
  orderType : OrderType
  actionType : ActionType
  priceScaleCode : BitVec 8
  orderDate : BitVec 32
  orderPriorityDate : BitVec 32
  orderPriorityTime : BitVec 32
  orderPriorityMicroSecs : BitVec 16
  orderOrigin : Alpha 1
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace OrderUpdateMarketSheetMessage

def encode (message : OrderUpdateMarketSheetMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.aggregatedVolume
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.linkId
    ++ (encodeUInt 4 message.orderId
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 2 message.numberOrders
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (ActionType.encode message.actionType
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 4 message.orderDate
    ++ (encodeUInt 4 message.orderPriorityDate
    ++ (encodeUInt 4 message.orderPriorityTime
    ++ (encodeUInt 2 message.orderPriorityMicroSecs
    ++ (Alpha.encode message.orderOrigin
    ++ (Alpha.encode message.reserved1))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderUpdateMarketSheetMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (aggregatedVolume, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (linkId, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (numberOrders, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (actionType, bytes) ← ActionType.decode bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (orderDate, bytes) ← decodeUInt 4 bytes
  let (orderPriorityDate, bytes) ← decodeUInt 4 bytes
  let (orderPriorityTime, bytes) ← decodeUInt 4 bytes
  let (orderPriorityMicroSecs, bytes) ← decodeUInt 2 bytes
  let (orderOrigin, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, price, aggregatedVolume, volume, linkId, orderId, systemId, sourceTimeMicroSecs, numberOrders, side, orderType, actionType, priceScaleCode, orderDate, orderPriorityDate, orderPriorityTime, orderPriorityMicroSecs, orderOrigin, reserved1 }, bytes)

@[simp] theorem encode_length (message : OrderUpdateMarketSheetMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, OrderType.encode_length, ActionType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderUpdateMarketSheetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdateMarketSheetMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ActionType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderUpdateMarketSheetMessage

/-- Order Book Retransmission Delimiter Message: 12 bytes -/
structure OrderBookRetransmissionDelimiterMessage where
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  applicationId : Alpha 2
  instanceNum : BitVec 8
  retransmissionIndicator : RetransmissionIndicator
  deriving DecidableEq, Repr

namespace OrderBookRetransmissionDelimiterMessage

def encode (message : OrderBookRetransmissionDelimiterMessage) : List UInt8 :=
  encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (Alpha.encode message.applicationId
    ++ (encodeUInt 1 message.instanceNum
    ++ (RetransmissionIndicator.encode message.retransmissionIndicator))))

def decode (bytes : List UInt8) : Option (OrderBookRetransmissionDelimiterMessage × List UInt8) := do
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (applicationId, bytes) ← Alpha.decode 2 bytes
  let (instanceNum, bytes) ← decodeUInt 1 bytes
  let (retransmissionIndicator, bytes) ← RetransmissionIndicator.decode bytes
  pure ({ sourceTime, sourceSeqNum, applicationId, instanceNum, retransmissionIndicator }, bytes)

@[simp] theorem encode_length (message : OrderBookRetransmissionDelimiterMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RetransmissionIndicator.encode_length]

theorem encode_length_pos (message : OrderBookRetransmissionDelimiterMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookRetransmissionDelimiterMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [RetransmissionIndicator.decode_encode, some_bind]
  rfl

end OrderBookRetransmissionDelimiterMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | orderUpdateMarketSheetMessage (message : OrderUpdateMarketSheetMessage) -- 230
  | orderBookRetransmissionDelimiterMessage (message : OrderBookRetransmissionDelimiterMessage) -- 231
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .orderUpdateMarketSheetMessage _ => 230
  | .orderBookRetransmissionDelimiterMessage _ => 231

def encode : Payload → List UInt8
  | .orderUpdateMarketSheetMessage message => OrderUpdateMarketSheetMessage.encode message
  | .orderBookRetransmissionDelimiterMessage message => OrderBookRetransmissionDelimiterMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 60 := by
  cases message with
  | orderUpdateMarketSheetMessage inner =>
    simp only [encode, OrderUpdateMarketSheetMessage.encode_length]
    omega
  | orderBookRetransmissionDelimiterMessage inner =>
    simp only [encode, OrderBookRetransmissionDelimiterMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 230 then (OrderUpdateMarketSheetMessage.decode bytes).map fun (message, rest) => (.orderUpdateMarketSheetMessage message, rest)
  else if tag = 231 then (OrderBookRetransmissionDelimiterMessage.decode bytes).map fun (message, rest) => (.orderBookRetransmissionDelimiterMessage message, rest)
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
  encodeUInt 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | orderUpdateMarketSheetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderUpdateMarketSheetMessage.encode_length]
    omega
  | orderBookRetransmissionDelimiterMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookRetransmissionDelimiterMessage.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Message Buffer -/
structure MessageBuffer (numberMsgEntries : BitVec 8) where
  message : Exact numberMsgEntries.toNat Message
  deriving DecidableEq, Repr

namespace MessageBuffer

def encode {numberMsgEntries : BitVec 8} (message : MessageBuffer numberMsgEntries) : List UInt8 :=
  encodeMany Message.encode message.message.val

def decode (numberMsgEntries : BitVec 8) (bytes : List UInt8) : Option (MessageBuffer numberMsgEntries × List UInt8) := do
  let (message_, bytes) ← decodeMany Message.decode numberMsgEntries.toNat bytes
  if fits_message : message_.length = numberMsgEntries.toNat then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

@[simp] theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) (rest : List UInt8) :
    decode numberMsgEntries (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeMany_exact numberMsgEntries.toNat Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (numberMsgEntries : BitVec 8) (message : MessageBuffer numberMsgEntries) : decode numberMsgEntries (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode numberMsgEntries message []

end MessageBuffer

/-- Message Buffer -/
structure MessageBufferZlib where
  payload : List UInt8
  deriving DecidableEq, Repr

namespace MessageBufferZlib

def encode (message : MessageBufferZlib) : List UInt8 :=
  encodeMany Byte.encode message.payload

def decode (bytes : List UInt8) : Option MessageBufferZlib := do
  let payload ← decodeAll Byte.decode bytes.length bytes
  pure { payload }

theorem decode_encode (message : MessageBufferZlib) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.payload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.payload), some_bind]
  rfl

end MessageBufferZlib

/-- The Message Buffer, as bytes when Delivery Flag says it was Zlib transformed and as it lies when it says it was not -/
inductive MessageBufferBody (numberMsgEntries : BitVec 8) where
  | zlib (tag : { v : BitVec 8 // 15 < v }) (message : MessageBufferZlib) -- 15 < tag
  | plain (tag : { v : BitVec 8 // ¬ (15 < v) }) (message : MessageBuffer numberMsgEntries) -- every other value
  deriving DecidableEq, Repr

namespace MessageBufferBody

/-- The Delivery Flag each body is read by -/
def tag {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → BitVec 8
  | .zlib tag _ => tag.val
  | .plain tag _ => tag.val

def encode {numberMsgEntries : BitVec 8} : MessageBufferBody numberMsgEntries → List UInt8
  | .zlib _ message => MessageBufferZlib.encode message
  | .plain _ message => MessageBuffer.encode message

/-- Decoded from the whole of what holds it: a body that reads to its end takes it all, any other must leave nothing -/
def decode (numberMsgEntries : BitVec 8) (tag : BitVec 8) (bytes : List UInt8) : Option (MessageBufferBody numberMsgEntries) :=
  if h : 15 < tag then (MessageBufferZlib.decode bytes).map fun message => .zlib ⟨tag, h⟩ message
  else (MessageBuffer.decode numberMsgEntries bytes).bind fun (message, rest) => if rest.isEmpty then some (.plain ⟨tag, h⟩ message) else none

theorem decode_encode (numberMsgEntries : BitVec 8) (message : MessageBufferBody numberMsgEntries) :
    decode numberMsgEntries (tag message) (encode message) = some message := by
  cases message with
  | zlib t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBufferZlib.decode_encode, Option.map_some]
  | plain t m =>
    obtain ⟨v, h⟩ := t
    simp only [tag, encode, decode, h, reduceDIte, MessageBuffer.decode_encode_nil]
    rfl

end MessageBufferBody

/-- Packet -/
structure Packet where
  packetLength : BitVec 16
  packetType : BitVec 16
  packetSequenceNumber : BitVec 32
  sendTime : BitVec 32
  serviceId : BitVec 16
  numberMsgEntries : BitVec 8
  messageBuffer : MessageBufferBody numberMsgEntries
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 2 message.packetLength
    ++ (encodeUInt 2 message.packetType
    ++ (encodeUInt 4 message.packetSequenceNumber
    ++ (encodeUInt 4 message.sendTime
    ++ (encodeUInt 2 message.serviceId
    ++ (encodeUInt 1 (MessageBufferBody.tag message.messageBuffer)
    ++ (encodeUInt 1 message.numberMsgEntries
    ++ (MessageBufferBody.encode message.messageBuffer)))))))

def decode (bytes : List UInt8) : Option Packet := do
  let (packetLength, bytes) ← decodeUInt 2 bytes
  let (packetType, bytes) ← decodeUInt 2 bytes
  let (packetSequenceNumber, bytes) ← decodeUInt 4 bytes
  let (sendTime, bytes) ← decodeUInt 4 bytes
  let (serviceId, bytes) ← decodeUInt 2 bytes
  let (deliveryFlag, bytes) ← decodeUInt 1 bytes
  let (numberMsgEntries, bytes) ← decodeUInt 1 bytes
  let messageBuffer ← MessageBufferBody.decode numberMsgEntries deliveryFlag bytes
  pure { packetLength, packetType, packetSequenceNumber, sendTime, serviceId, numberMsgEntries, messageBuffer }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MessageBufferBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.GpwWseOrderbookXdpV68
