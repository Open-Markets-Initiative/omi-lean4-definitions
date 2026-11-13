import Wire

/-!
# Philippine Stock Exchange Pse Equities Itch Basic With Last Sale v2.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count
and the encoder never writes it

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as
a count and the encoder never writes it

License: MIT No Attribution
-/

namespace Omi.PsePseequitiesBasicwithlastsaleItchV23

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x52, 0x51, 0x41, 0x42, 0x4C, 0x4A, 0x50, 0x4D, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | preOpenNoCancellationPeriod -- Pre Open No Cancellation Period
  | startOfMarketHours -- Start Of Market Hours
  | scheduledBreakBegins -- Scheduled Break Begins
  | scheduledBreakEnds -- Scheduled Break Ends
  | preCloseCommences -- Pre Close Commences
  | preCloseNoCancellationPeriod -- Pre Close No Cancellation Period
  | tradingAtLast -- Trading At Last
  | endOfMarketHours -- End Of Market Hours
  | endOfTrading -- End Of Trading
  | endOfSystemMessages -- End Of System Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .preOpenNoCancellationPeriod => 0x52
  | .startOfMarketHours => 0x51
  | .scheduledBreakBegins => 0x41
  | .scheduledBreakEnds => 0x42
  | .preCloseCommences => 0x4C
  | .preCloseNoCancellationPeriod => 0x4A
  | .tradingAtLast => 0x50
  | .endOfMarketHours => 0x4D
  | .endOfTrading => 0x45
  | .endOfSystemMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x52 then .preOpenNoCancellationPeriod
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x41 then .scheduledBreakBegins
  else if byte = 0x42 then .scheduledBreakEnds
  else if byte = 0x4C then .preCloseCommences
  else if byte = 0x4A then .preCloseNoCancellationPeriod
  else if byte = 0x50 then .tradingAtLast
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x45 then .endOfTrading
  else .endOfSystemMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | preOpenNoCancellationPeriod => decide
  | startOfMarketHours => decide
  | scheduledBreakBegins => decide
  | scheduledBreakEnds => decide
  | preCloseCommences => decide
  | preCloseNoCancellationPeriod => decide
  | tradingAtLast => decide
  | endOfMarketHours => decide
  | endOfTrading => decide
  | endOfSystemMessages => decide
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

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x55, 0x50]

inductive PriceType where
  | perUnit -- Per Unit
  | percentage -- Percentage
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .perUnit => 0x55
  | .percentage => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x55 then .perUnit
  else .percentage

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | perUnit => decide
  | percentage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x43, 0x50, 0x57, 0x45, 0x44, 0x49]

inductive InstrumentType where
  | commonStock -- Common Stock
  | preferredStock -- Preferred Stock
  | warrant -- Warrant
  | etf -- Etf
  | pdr -- Pdr
  | index -- Index
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .commonStock => 0x43
  | .preferredStock => 0x50
  | .warrant => 0x57
  | .etf => 0x45
  | .pdr => 0x44
  | .index => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x43 then .commonStock
  else if byte = 0x50 then .preferredStock
  else if byte = 0x57 then .warrant
  else if byte = 0x45 then .etf
  else if byte = 0x44 then .pdr
  else .index

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | commonStock => decide
  | preferredStock => decide
  | warrant => decide
  | etf => decide
  | pdr => decide
  | index => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Short Sell Eligible: one byte code -/
def ShortSellEligible.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ShortSellEligible where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSellEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSellEligible

def toByte : ShortSellEligible → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSellEligible :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : ShortSellEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSellEligible) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSellEligible) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSellEligible × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSellEligible) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ShortSellEligible) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ShortSellEligible) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSellEligible

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56]

inductive TradingState where
  | trading -- Trading
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .trading => 0x54
  | .suspended => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .trading
  else .suspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x4E, 0x53, 0x46, 0x48]

inductive Reason where
  | normalTrading -- Normal Trading
  | suspendedByMarketControl -- Suspended By Market Control
  | frozenDueToCircuitBreaker -- Frozen Due To Circuit Breaker
  | halted -- Halted
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .normalTrading => 0x4E
  | .suspendedByMarketControl => 0x53
  | .frozenDueToCircuitBreaker => 0x46
  | .halted => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x4E then .normalTrading
  else if byte = 0x53 then .suspendedByMarketControl
  else if byte = 0x46 then .frozenDueToCircuitBreaker
  else .halted

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | suspendedByMarketControl => decide
  | frozenDueToCircuitBreaker => decide
  | halted => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Reason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Printable) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Trade Indicator: one byte code -/
def TradeIndicator.codes : List UInt8 :=
  [0x20, 0x43, 0x42, 0x4D]

inductive TradeIndicator where
  | regularTrade -- Regular Trade
  | intentionalCrossTrade -- Intentional Cross Trade
  | blockSale -- Block Sale
  | manualTrade -- Manual Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeIndicator

def toByte : TradeIndicator → UInt8
  | .regularTrade => 0x20
  | .intentionalCrossTrade => 0x43
  | .blockSale => 0x42
  | .manualTrade => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeIndicator :=
  if byte = 0x20 then .regularTrade
  else if byte = 0x43 then .intentionalCrossTrade
  else if byte = 0x42 then .blockSale
  else .manualTrade

def ofByte (byte : UInt8) : TradeIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeIndicator) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | intentionalCrossTrade => decide
  | blockSale => decide
  | manualTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeIndicator

/-- Time Stamp Seconds Message: 4 bytes -/
structure TimeStampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeStampSecondsMessage

def encode (message : TimeStampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeStampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeStampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeStampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeStampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeStampSecondsMessage

/-- System Event Message: 17 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, group, eventCode, orderbook }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Trading Schedule Message: 21 bytes -/
structure TradingScheduleMessage where
  timestamp : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  scheduledTime : BitVec 32
  deriving DecidableEq, Repr

namespace TradingScheduleMessage

def encode (message : TradingScheduleMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.scheduledTime))))

def decode (bytes : List UInt8) : Option (TradingScheduleMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (scheduledTime, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, group, eventCode, orderbook, scheduledTime }, bytes)

@[simp] theorem encode_length (message : TradingScheduleMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : TradingScheduleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingScheduleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingScheduleMessage

/-- Price Tick Size Message: 16 bytes -/
structure PriceTickSizeMessage where
  timestamp : BitVec 32
  tickSizeTableId : BitVec 32
  tickSizeInteger4 : BitVec 32
  priceStart : BitVec 32
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 4 message.tickSizeInteger4
    ++ (encodeUInt 4 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (tickSizeInteger4, bytes) ← decodeUInt 4 bytes
  let (priceStart, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, tickSizeTableId, tickSizeInteger4, priceStart }, bytes)

@[simp] theorem encode_length (message : PriceTickSizeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceTickSizeMessage

/-- Quantity Tick Size Message: 24 bytes -/
structure QuantityTickSizeMessage where
  timestamp : BitVec 32
  tickSizeTableId : BitVec 32
  tickSizeInteger8 : BitVec 64
  quantityStart : BitVec 64
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 8 message.tickSizeInteger8
    ++ (encodeUInt 8 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (tickSizeInteger8, bytes) ← decodeUInt 8 bytes
  let (quantityStart, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, tickSizeTableId, tickSizeInteger8, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuantityTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityTickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuantityTickSizeMessage

/-- Orderbook Directory Message: 89 bytes -/
structure OrderbookDirectoryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  priceType : PriceType
  isin : Alpha 12
  secCode : Alpha 12
  currency : Alpha 3
  group : Alpha 8
  lotSize : BitVec 64
  quantityTickSizeTableId : BitVec 32
  priceTickSizeTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingDate : BitVec 32
  delistingTime : BitVec 32
  instrumentType : InstrumentType
  shares : BitVec 64
  productCode : Alpha 8
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (PriceType.encode message.priceType
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.secCode
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 8 message.lotSize
    ++ (encodeUInt 4 message.quantityTickSizeTableId
    ++ (encodeUInt 4 message.priceTickSizeTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (InstrumentType.encode message.instrumentType
    ++ (encodeUInt 8 message.shares
    ++ (Alpha.encode message.productCode)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (secCode, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (lotSize, bytes) ← decodeUInt 8 bytes
  let (quantityTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (shares, bytes) ← decodeUInt 8 bytes
  let (productCode, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, orderbook, priceType, isin, secCode, currency, group, lotSize, quantityTickSizeTableId, priceTickSizeTableId, priceDecimals, delistingDate, delistingTime, instrumentType, shares, productCode }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, Alpha.encode_length, InstrumentType.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Orderbook Restrictions Message: 29 bytes -/
structure OrderbookRestrictionsMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  shortSellEligible : ShortSellEligible
  highCollar : BitVec 32
  lowCollar : BitVec 32
  cbLimitUp : BitVec 32
  cbLimitDown : BitVec 32
  cbLimitDecimals : BitVec 32
  deriving DecidableEq, Repr

namespace OrderbookRestrictionsMessage

def encode (message : OrderbookRestrictionsMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (ShortSellEligible.encode message.shortSellEligible
    ++ (encodeUInt 4 message.highCollar
    ++ (encodeUInt 4 message.lowCollar
    ++ (encodeUInt 4 message.cbLimitUp
    ++ (encodeUInt 4 message.cbLimitDown
    ++ (encodeUInt 4 message.cbLimitDecimals)))))))

def decode (bytes : List UInt8) : Option (OrderbookRestrictionsMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (shortSellEligible, bytes) ← ShortSellEligible.decode bytes
  let (highCollar, bytes) ← decodeUInt 4 bytes
  let (lowCollar, bytes) ← decodeUInt 4 bytes
  let (cbLimitUp, bytes) ← decodeUInt 4 bytes
  let (cbLimitDown, bytes) ← decodeUInt 4 bytes
  let (cbLimitDecimals, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderbook, shortSellEligible, highCollar, lowCollar, cbLimitUp, cbLimitDown, cbLimitDecimals }, bytes)

@[simp] theorem encode_length (message : OrderbookRestrictionsMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ShortSellEligible.encode_length]

theorem encode_length_pos (message : OrderbookRestrictionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookRestrictionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ShortSellEligible.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderbookRestrictionsMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  reason : Reason
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (Reason.encode message.reason)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ timestamp, orderbook, tradingState, reason }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OrderbookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Trade Message: 30 bytes -/
structure TradeMessage where
  timestamp : BitVec 32
  executedQuantity : BitVec 64
  orderbook : BitVec 32
  printable : Printable
  executionPrice : BitVec 32
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  pure ({ timestamp, executedQuantity, orderbook, printable := printable_, executionPrice, matchNumber, tradeIndicator }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, TradeIndicator.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradeIndicator.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Trade With Broker Id Message: 38 bytes -/
structure TradeWithBrokerIdMessage where
  timestamp : BitVec 32
  executedQuantity : BitVec 64
  orderbook : BitVec 32
  printable : Printable
  executionPrice : BitVec 32
  matchNumber : BitVec 64
  tradeIndicator : TradeIndicator
  buyBrokerId : Alpha 4
  sellBrokerId : Alpha 4
  deriving DecidableEq, Repr

namespace TradeWithBrokerIdMessage

def encode (message : TradeWithBrokerIdMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.executionPrice
    ++ (encodeUInt 8 message.matchNumber
    ++ (TradeIndicator.encode message.tradeIndicator
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId))))))))

def decode (bytes : List UInt8) : Option (TradeWithBrokerIdMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 8 bytes
  let (tradeIndicator, bytes) ← TradeIndicator.decode bytes
  let (buyBrokerId, bytes) ← Alpha.decode 4 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, executedQuantity, orderbook, printable := printable_, executionPrice, matchNumber, tradeIndicator, buyBrokerId, sellBrokerId }, bytes)

@[simp] theorem encode_length (message : TradeWithBrokerIdMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, TradeIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeWithBrokerIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeWithBrokerIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeWithBrokerIdMessage

/-- Bbo Quotation Message: 32 bytes -/
structure BboQuotationMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  bestBidPrice : BitVec 32
  bestBidSize : BitVec 64
  bestOfferPrice : BitVec 32
  bestOfferSize : BitVec 64
  deriving DecidableEq, Repr

namespace BboQuotationMessage

def encode (message : BboQuotationMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 8 message.bestBidSize
    ++ (encodeUInt 4 message.bestOfferPrice
    ++ (encodeUInt 8 message.bestOfferSize)))))

def decode (bytes : List UInt8) : Option (BboQuotationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidSize, bytes) ← decodeUInt 8 bytes
  let (bestOfferPrice, bytes) ← decodeUInt 4 bytes
  let (bestOfferSize, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, orderbook, bestBidPrice, bestBidSize, bestOfferPrice, bestOfferSize }, bytes)

@[simp] theorem encode_length (message : BboQuotationMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BboQuotationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BboQuotationMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BboQuotationMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | tradingScheduleMessage (message : TradingScheduleMessage) -- "s" 0x73
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- "L" 0x4C
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- "M" 0x4D
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | orderbookRestrictionsMessage (message : OrderbookRestrictionsMessage) -- "k" 0x6B
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- "H" 0x48
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | tradeWithBrokerIdMessage (message : TradeWithBrokerIdMessage) -- "p" 0x70
  | bboQuotationMessage (message : BboQuotationMessage) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .tradingScheduleMessage _ => 115
  | .priceTickSizeMessage _ => 76
  | .quantityTickSizeMessage _ => 77
  | .orderbookDirectoryMessage _ => 82
  | .orderbookRestrictionsMessage _ => 107
  | .orderbookTradingActionMessage _ => 72
  | .tradeMessage _ => 80
  | .tradeWithBrokerIdMessage _ => 112
  | .bboQuotationMessage _ => 79

def encode : Payload → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .tradingScheduleMessage message => TradingScheduleMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .orderbookRestrictionsMessage message => OrderbookRestrictionsMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeWithBrokerIdMessage message => TradeWithBrokerIdMessage.encode message
  | .bboQuotationMessage message => BboQuotationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 89 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | tradingScheduleMessage inner =>
    simp only [encode, TradingScheduleMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookRestrictionsMessage inner =>
    simp only [encode, OrderbookRestrictionsMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeWithBrokerIdMessage inner =>
    simp only [encode, TradeWithBrokerIdMessage.encode_length]
    omega
  | bboQuotationMessage inner =>
    simp only [encode, BboQuotationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 115 then (TradingScheduleMessage.decode bytes).map fun (message, rest) => (.tradingScheduleMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 107 then (OrderbookRestrictionsMessage.decode bytes).map fun (message, rest) => (.orderbookRestrictionsMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 112 then (TradeWithBrokerIdMessage.decode bytes).map fun (message, rest) => (.tradeWithBrokerIdMessage message, rest)
  else if tag = 79 then (BboQuotationMessage.decode bytes).map fun (message, rest) => (.bboQuotationMessage message, rest)
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
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
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
  | timeStampSecondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | tradingScheduleMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingScheduleMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookRestrictionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookRestrictionsMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeWithBrokerIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeWithBrokerIdMessage.encode_length]
    omega
  | bboQuotationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BboQuotationMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
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

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.PsePseequitiesBasicwithlastsaleItchV23
