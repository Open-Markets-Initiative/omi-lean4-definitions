import Wire

/-!
# Moscow Exchange SIMBA Spectra Futures Instrument Incremental v9.9.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MoexSpectraFutinfoincrementalSimbaV990

/-- Market Segment Id: one byte code -/
def MarketSegmentId.codes : List UInt8 :=
  [0x44]

inductive MarketSegmentId where
  | derivatives -- Derivatives
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketSegmentId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketSegmentId

def toByte : MarketSegmentId → UInt8
  | .derivatives => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : MarketSegmentId :=
  .derivatives

def ofByte (byte : UInt8) : MarketSegmentId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketSegmentId) : ofByte value.toByte = value := by
  cases value with
  | derivatives => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketSegmentId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketSegmentId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketSegmentId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketSegmentId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketSegmentId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketSegmentId

/-- Market Data Packet Header: 16 bytes -/
structure MarketDataPacketHeader where
  msgSeqNum : BitVec 32
  msgSize : BitVec 16
  msgFlags : BitVec 16
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MarketDataPacketHeader

def encode (message : MarketDataPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 message.msgFlags
    ++ (encodeUIntLE 8 message.sendingTime)))

def decode (bytes : List UInt8) : Option (MarketDataPacketHeader × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgFlags, bytes) ← decodeUIntLE 2 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ msgSeqNum, msgSize, msgFlags, sendingTime }, bytes)

@[simp] theorem encode_length (message : MarketDataPacketHeader) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketDataPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketDataPacketHeader

/-- Incremental Packet Header: 12 bytes -/
structure IncrementalPacketHeader where
  transactTime : BitVec 64
  exchangeTradingSessionId : BitVec 32
  deriving DecidableEq, Repr

namespace IncrementalPacketHeader

def encode (message : IncrementalPacketHeader) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.exchangeTradingSessionId)

def decode (bytes : List UInt8) : Option (IncrementalPacketHeader × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (exchangeTradingSessionId, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, exchangeTradingSessionId }, bytes)

@[simp] theorem encode_length (message : IncrementalPacketHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IncrementalPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IncrementalPacketHeader

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Security Status Message: 86 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 32
  symbol : Alpha 25
  securityTradingStatus : BitVec 8
  highLimitPx : BitVec 64
  lowLimitPx : BitVec 64
  initialMarginOnBuy : BitVec 64
  initialMarginOnSell : BitVec 64
  initialMarginSyntetic : BitVec 64
  highLimitPxWeekend : BitVec 64
  lowLimitPxWeekend : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUIntLE 8 message.highLimitPx
    ++ (encodeUIntLE 8 message.lowLimitPx
    ++ (encodeUIntLE 8 message.initialMarginOnBuy
    ++ (encodeUIntLE 8 message.initialMarginOnSell
    ++ (encodeUIntLE 8 message.initialMarginSyntetic
    ++ (encodeUIntLE 8 message.highLimitPxWeekend
    ++ (encodeUIntLE 8 message.lowLimitPxWeekend)))))))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 25 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (highLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnBuy, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginOnSell, bytes) ← decodeUIntLE 8 bytes
  let (initialMarginSyntetic, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPxWeekend, bytes) ← decodeUIntLE 8 bytes
  let (lowLimitPxWeekend, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, symbol, securityTradingStatus, highLimitPx, lowLimitPx, initialMarginOnBuy, initialMarginOnSell, initialMarginSyntetic, highLimitPxWeekend, lowLimitPxWeekend }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Trading Session Status Message: 48 bytes -/
structure TradingSessionStatusMessage where
  tradSesOpenTime : BitVec 64
  tradSesCloseTime : BitVec 64
  tradingSessionId : BitVec 8
  exchangeTradingSessionIdInt32NullOptional : BitVec 32
  tradSesStatus : BitVec 8
  marketSegmentId : MarketSegmentId
  tradSesEvent : BitVec 8
  tradePeriodId : BitVec 64
  settlSessBegin : BitVec 64
  clrSessBegin : BitVec 64
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.tradSesCloseTime
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32NullOptional
    ++ (encodeUInt 1 message.tradSesStatus
    ++ (MarketSegmentId.encode message.marketSegmentId
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (encodeUIntLE 8 message.tradePeriodId
    ++ (encodeUIntLE 8 message.settlSessBegin
    ++ (encodeUIntLE 8 message.clrSessBegin)))))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (exchangeTradingSessionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← MarketSegmentId.decode bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (tradePeriodId, bytes) ← decodeUIntLE 8 bytes
  let (settlSessBegin, bytes) ← decodeUIntLE 8 bytes
  let (clrSessBegin, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradSesOpenTime, tradSesCloseTime, tradingSessionId, exchangeTradingSessionIdInt32NullOptional, tradSesStatus, marketSegmentId, tradSesEvent, tradePeriodId, settlSessBegin, clrSessBegin }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, MarketSegmentId.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MarketSegmentId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Underlying Symbol Text -/
structure UnderlyingSymbolText where
  underlyingSymbolTextData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace UnderlyingSymbolText

def encode (message : UnderlyingSymbolText) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.underlyingSymbolTextData.val.length)
    ++ (encodeMany Byte.encode message.underlyingSymbolTextData.val)

def decode (bytes : List UInt8) : Option (UnderlyingSymbolText × List UInt8) := do
  let (underlyingSymbolTextLength, bytes) ← decodeUIntLE 2 bytes
  let (underlyingSymbolTextData_, bytes) ← decodeMany Byte.decode underlyingSymbolTextLength.toNat bytes
  if fits_underlyingSymbolTextData : underlyingSymbolTextData_.length < 256 ^ 2 then
    pure ({ underlyingSymbolTextData := ⟨underlyingSymbolTextData_, fits_underlyingSymbolTextData⟩ }, bytes)
  else none

theorem encode_length_pos (message : UnderlyingSymbolText) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnderlyingSymbolText) : (encode message).length ≤ 65537 := by
  have bound_underlyingSymbolTextData := message.underlyingSymbolTextData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : UnderlyingSymbolText) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.underlyingSymbolTextData.length_lt]
  rfl

end UnderlyingSymbolText

/-- Discrete Auction Message No Underlyings Group -/
structure DiscreteAuctionMessageNoUnderlyingsGroup where
  underlyingSymbolText : UnderlyingSymbolText
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessageNoUnderlyingsGroup

def encode (message : DiscreteAuctionMessageNoUnderlyingsGroup) : List UInt8 :=
  UnderlyingSymbolText.encode message.underlyingSymbolText

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessageNoUnderlyingsGroup × List UInt8) := do
  let (underlyingSymbolText, bytes) ← UnderlyingSymbolText.decode bytes
  pure ({ underlyingSymbolText }, bytes)

theorem encode_length_pos (message : DiscreteAuctionMessageNoUnderlyingsGroup) : (encode message).length > 0 := by
  have positive := UnderlyingSymbolText.encode_length_pos message.underlyingSymbolText
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessageNoUnderlyingsGroup) : (encode message).length ≤ 65537 := by
  have bound_underlyingSymbolText := UnderlyingSymbolText.encode_length_le message.underlyingSymbolText
  unfold encode
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessageNoUnderlyingsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [UnderlyingSymbolText.decode_encode, some_bind]
  rfl

end DiscreteAuctionMessageNoUnderlyingsGroup

/-- Discrete Auction Message No Underlyings Groups -/
structure DiscreteAuctionMessageNoUnderlyingsGroups where
  blockLength : BitVec 16
  discreteAuctionMessageNoUnderlyingsGroup : Bounded 1 DiscreteAuctionMessageNoUnderlyingsGroup
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessageNoUnderlyingsGroups

def encode (message : DiscreteAuctionMessageNoUnderlyingsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.discreteAuctionMessageNoUnderlyingsGroup.val.length)
    ++ (encodeMany DiscreteAuctionMessageNoUnderlyingsGroup.encode message.discreteAuctionMessageNoUnderlyingsGroup.val))

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessageNoUnderlyingsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint8, bytes) ← decodeUInt 1 bytes
  let (discreteAuctionMessageNoUnderlyingsGroup_, bytes) ← decodeMany DiscreteAuctionMessageNoUnderlyingsGroup.decode numInGroupUint8.toNat bytes
  if fits_discreteAuctionMessageNoUnderlyingsGroup : discreteAuctionMessageNoUnderlyingsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, discreteAuctionMessageNoUnderlyingsGroup := ⟨discreteAuctionMessageNoUnderlyingsGroup_, fits_discreteAuctionMessageNoUnderlyingsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : DiscreteAuctionMessageNoUnderlyingsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessageNoUnderlyingsGroups) : (encode message).length ≤ 16711938 := by
  have bound_discreteAuctionMessageNoUnderlyingsGroup := message.discreteAuctionMessageNoUnderlyingsGroup.length_lt
  have bound_discreteAuctionMessageNoUnderlyingsGroup_items := encodeMany_length_le DiscreteAuctionMessageNoUnderlyingsGroup.encode 65537 DiscreteAuctionMessageNoUnderlyingsGroup.encode_length_le message.discreteAuctionMessageNoUnderlyingsGroup.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessageNoUnderlyingsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 DiscreteAuctionMessageNoUnderlyingsGroup.encode DiscreteAuctionMessageNoUnderlyingsGroup.decode DiscreteAuctionMessageNoUnderlyingsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.discreteAuctionMessageNoUnderlyingsGroup.length_lt]
  rfl

end DiscreteAuctionMessageNoUnderlyingsGroups

/-- Discrete Auction Message -/
structure DiscreteAuctionMessage where
  tradSesOpenTime : BitVec 64
  tradSesCloseTimeFrom : BitVec 64
  tradSesCloseTimeTill : BitVec 64
  auctionId : BitVec 64
  exchangeTradingSessionIdInt32 : BitVec 32
  eventIdOpen : BitVec 32
  eventIdClose : BitVec 32
  tradePeriodId : BitVec 64
  discreteAuctionMessageNoUnderlyingsGroups : DiscreteAuctionMessageNoUnderlyingsGroups
  deriving DecidableEq, Repr

namespace DiscreteAuctionMessage

def encode (message : DiscreteAuctionMessage) : List UInt8 :=
  encodeUIntLE 8 message.tradSesOpenTime
    ++ (encodeUIntLE 8 message.tradSesCloseTimeFrom
    ++ (encodeUIntLE 8 message.tradSesCloseTimeTill
    ++ (encodeUIntLE 8 message.auctionId
    ++ (encodeUIntLE 4 message.exchangeTradingSessionIdInt32
    ++ (encodeUIntLE 4 message.eventIdOpen
    ++ (encodeUIntLE 4 message.eventIdClose
    ++ (encodeUIntLE 8 message.tradePeriodId
    ++ (DiscreteAuctionMessageNoUnderlyingsGroups.encode message.discreteAuctionMessageNoUnderlyingsGroups))))))))

def decode (bytes : List UInt8) : Option (DiscreteAuctionMessage × List UInt8) := do
  let (tradSesOpenTime, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTimeFrom, bytes) ← decodeUIntLE 8 bytes
  let (tradSesCloseTimeTill, bytes) ← decodeUIntLE 8 bytes
  let (auctionId, bytes) ← decodeUIntLE 8 bytes
  let (exchangeTradingSessionIdInt32, bytes) ← decodeUIntLE 4 bytes
  let (eventIdOpen, bytes) ← decodeUIntLE 4 bytes
  let (eventIdClose, bytes) ← decodeUIntLE 4 bytes
  let (tradePeriodId, bytes) ← decodeUIntLE 8 bytes
  let (discreteAuctionMessageNoUnderlyingsGroups, bytes) ← DiscreteAuctionMessageNoUnderlyingsGroups.decode bytes
  pure ({ tradSesOpenTime, tradSesCloseTimeFrom, tradSesCloseTimeTill, auctionId, exchangeTradingSessionIdInt32, eventIdOpen, eventIdClose, tradePeriodId, discreteAuctionMessageNoUnderlyingsGroups }, bytes)

theorem encode_length_pos (message : DiscreteAuctionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DiscreteAuctionMessage) : (encode message).length ≤ 16711990 := by
  have bound_discreteAuctionMessageNoUnderlyingsGroups := DiscreteAuctionMessageNoUnderlyingsGroups.encode_length_le message.discreteAuctionMessageNoUnderlyingsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : DiscreteAuctionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [DiscreteAuctionMessageNoUnderlyingsGroups.decode_encode, some_bind]
  rfl

end DiscreteAuctionMessage

/-- Security Mass Status Message No Related Sym Group: 5 bytes -/
structure SecurityMassStatusMessageNoRelatedSymGroup where
  securityId : BitVec 32
  securityTradingStatus : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityMassStatusMessageNoRelatedSymGroup

def encode (message : SecurityMassStatusMessageNoRelatedSymGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ (encodeUInt 1 message.securityTradingStatus)

def decode (bytes : List UInt8) : Option (SecurityMassStatusMessageNoRelatedSymGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  pure ({ securityId, securityTradingStatus }, bytes)

@[simp] theorem encode_length (message : SecurityMassStatusMessageNoRelatedSymGroup) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityMassStatusMessageNoRelatedSymGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityMassStatusMessageNoRelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecurityMassStatusMessageNoRelatedSymGroup

/-- Security Mass Status Message No Related Sym Groups -/
structure SecurityMassStatusMessageNoRelatedSymGroups where
  blockLength : BitVec 16
  securityMassStatusMessageNoRelatedSymGroup : Bounded 2 SecurityMassStatusMessageNoRelatedSymGroup
  deriving DecidableEq, Repr

namespace SecurityMassStatusMessageNoRelatedSymGroups

def encode (message : SecurityMassStatusMessageNoRelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.securityMassStatusMessageNoRelatedSymGroup.val.length)
    ++ (encodeMany SecurityMassStatusMessageNoRelatedSymGroup.encode message.securityMassStatusMessageNoRelatedSymGroup.val))

def decode (bytes : List UInt8) : Option (SecurityMassStatusMessageNoRelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroupUint16, bytes) ← decodeUIntLE 2 bytes
  let (securityMassStatusMessageNoRelatedSymGroup_, bytes) ← decodeMany SecurityMassStatusMessageNoRelatedSymGroup.decode numInGroupUint16.toNat bytes
  if fits_securityMassStatusMessageNoRelatedSymGroup : securityMassStatusMessageNoRelatedSymGroup_.length < 256 ^ 2 then
    pure ({ blockLength, securityMassStatusMessageNoRelatedSymGroup := ⟨securityMassStatusMessageNoRelatedSymGroup_, fits_securityMassStatusMessageNoRelatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SecurityMassStatusMessageNoRelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityMassStatusMessageNoRelatedSymGroups) : (encode message).length ≤ 327679 := by
  have bound_securityMassStatusMessageNoRelatedSymGroup := message.securityMassStatusMessageNoRelatedSymGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const SecurityMassStatusMessageNoRelatedSymGroup.encode 5 SecurityMassStatusMessageNoRelatedSymGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityMassStatusMessageNoRelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SecurityMassStatusMessageNoRelatedSymGroup.encode SecurityMassStatusMessageNoRelatedSymGroup.decode SecurityMassStatusMessageNoRelatedSymGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityMassStatusMessageNoRelatedSymGroup.length_lt]
  rfl

end SecurityMassStatusMessageNoRelatedSymGroups

/-- Security Mass Status Message -/
structure SecurityMassStatusMessage where
  securityMassStatusMessageNoRelatedSymGroups : SecurityMassStatusMessageNoRelatedSymGroups
  deriving DecidableEq, Repr

namespace SecurityMassStatusMessage

def encode (message : SecurityMassStatusMessage) : List UInt8 :=
  SecurityMassStatusMessageNoRelatedSymGroups.encode message.securityMassStatusMessageNoRelatedSymGroups

def decode (bytes : List UInt8) : Option (SecurityMassStatusMessage × List UInt8) := do
  let (securityMassStatusMessageNoRelatedSymGroups, bytes) ← SecurityMassStatusMessageNoRelatedSymGroups.decode bytes
  pure ({ securityMassStatusMessageNoRelatedSymGroups }, bytes)

theorem encode_length_pos (message : SecurityMassStatusMessage) : (encode message).length > 0 := by
  have positive := SecurityMassStatusMessageNoRelatedSymGroups.encode_length_pos message.securityMassStatusMessageNoRelatedSymGroups
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityMassStatusMessage) : (encode message).length ≤ 327679 := by
  have bound_securityMassStatusMessageNoRelatedSymGroups := SecurityMassStatusMessageNoRelatedSymGroups.encode_length_le message.securityMassStatusMessageNoRelatedSymGroups
  unfold encode
  omega

@[simp] theorem decode_encode (message : SecurityMassStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SecurityMassStatusMessageNoRelatedSymGroups.decode_encode, some_bind]
  rfl

end SecurityMassStatusMessage

/-- Security Group Status Message: 38 bytes -/
structure SecurityGroupStatusMessage where
  securityGroupId : BitVec 64
  haltType : BitVec 8
  tradeModeMask : BitVec 32
  groupMaskInt64NullOptional : BitVec 64
  sectionIdInt32NullOptional : BitVec 32
  baseContractIdInt32NullOptional : BitVec 32
  securityTradingStatus : BitVec 8
  statusChangeTime : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityGroupStatusMessage

def encode (message : SecurityGroupStatusMessage) : List UInt8 :=
  encodeUIntLE 8 message.securityGroupId
    ++ (encodeUInt 1 message.haltType
    ++ (encodeUIntLE 4 message.tradeModeMask
    ++ (encodeUIntLE 8 message.groupMaskInt64NullOptional
    ++ (encodeUIntLE 4 message.sectionIdInt32NullOptional
    ++ (encodeUIntLE 4 message.baseContractIdInt32NullOptional
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (encodeUIntLE 8 message.statusChangeTime)))))))

def decode (bytes : List UInt8) : Option (SecurityGroupStatusMessage × List UInt8) := do
  let (securityGroupId, bytes) ← decodeUIntLE 8 bytes
  let (haltType, bytes) ← decodeUInt 1 bytes
  let (tradeModeMask, bytes) ← decodeUIntLE 4 bytes
  let (groupMaskInt64NullOptional, bytes) ← decodeUIntLE 8 bytes
  let (sectionIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (baseContractIdInt32NullOptional, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (statusChangeTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityGroupId, haltType, tradeModeMask, groupMaskInt64NullOptional, sectionIdInt32NullOptional, baseContractIdInt32NullOptional, securityTradingStatus, statusChangeTime }, bytes)

@[simp] theorem encode_length (message : SecurityGroupStatusMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SecurityGroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityGroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityGroupStatusMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | sequenceResetMessage (message : SequenceResetMessage) -- 2
  | securityStatusMessage (message : SecurityStatusMessage) -- 28
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 26
  | discreteAuctionMessage (message : DiscreteAuctionMessage) -- 24
  | securityMassStatusMessage (message : SecurityMassStatusMessage) -- 19
  | securityGroupStatusMessage (message : SecurityGroupStatusMessage) -- 22
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .heartbeatMessage _ => 1
  | .sequenceResetMessage _ => 2
  | .securityStatusMessage _ => 28
  | .tradingSessionStatusMessage _ => 26
  | .discreteAuctionMessage _ => 24
  | .securityMassStatusMessage _ => 19
  | .securityGroupStatusMessage _ => 22

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .discreteAuctionMessage message => DiscreteAuctionMessage.encode message
  | .securityMassStatusMessage message => SecurityMassStatusMessage.encode message
  | .securityGroupStatusMessage message => SecurityGroupStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 16711990 := by
  cases message with
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | discreteAuctionMessage inner =>
    have bound_inner := DiscreteAuctionMessage.encode_length_le inner
    simp only [encode]
    omega
  | securityMassStatusMessage inner =>
    have bound_inner := SecurityMassStatusMessage.encode_length_le inner
    simp only [encode]
    omega
  | securityGroupStatusMessage inner =>
    simp only [encode, SecurityGroupStatusMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 28 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 26 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 24 then (DiscreteAuctionMessage.decode bytes).map fun (message, rest) => (.discreteAuctionMessage message, rest)
  else if tag = 19 then (SecurityMassStatusMessage.decode bytes).map fun (message, rest) => (.securityMassStatusMessage message, rest)
  else if tag = 22 then (SecurityGroupStatusMessage.decode bytes).map fun (message, rest) => (.securityGroupStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 16711998 := by
  unfold encode
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TradingSessionStatusMessage.encode_length]
    omega
  | discreteAuctionMessage inner =>
    have bound_inner := DiscreteAuctionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityMassStatusMessage inner =>
    have bound_inner := SecurityMassStatusMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | securityGroupStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SecurityGroupStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Udp Packet -/
structure UdpPacket where
  marketDataPacketHeader : MarketDataPacketHeader
  incrementalPacketHeader : IncrementalPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  MarketDataPacketHeader.encode message.marketDataPacketHeader
    ++ (IncrementalPacketHeader.encode message.incrementalPacketHeader
    ++ (encodeMany Message.encode message.message))

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (marketDataPacketHeader, bytes) ← MarketDataPacketHeader.decode bytes
  let (incrementalPacketHeader, bytes) ← IncrementalPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { marketDataPacketHeader, incrementalPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [MarketDataPacketHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [MarketDataPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [IncrementalPacketHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end UdpPacket

end Omi.MoexSpectraFutinfoincrementalSimbaV990
