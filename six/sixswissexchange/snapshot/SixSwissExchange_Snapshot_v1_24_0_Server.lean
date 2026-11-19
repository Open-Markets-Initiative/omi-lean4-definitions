import Wire

/-!
# SIX Swiss Exchange SIX Swiss Exchange IMI Orderbook Snapshot Recovery Service v1.24.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads

Note: a Server Soup Bin Tcp Packet that ends the session is the last of serverSoupBinTcpPacket: the
decoder turns away one that is followed, and the record carries the proof it is not

License: MIT No Attribution
-/

namespace Omi.SixSixswissexchangeSnapshotGlimpseV1240Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RejectReasonCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x45, 0x49, 0x4D, 0x4F, 0x51, 0x53, 0x55, 0x56, 0x54, 0x4C, 0x20]

inductive EventCode where
  | break_ -- Break
  | resumptionAfterBreak -- Resumption After Break
  | endOfMessages -- End Of Messages
  | endOfSystemHours -- End Of System Hours
  | startOfAccepting -- Start Of Accepting
  | endOfMarketHours -- End Of Market Hours
  | startOfMessages -- Start Of Messages
  | startOfMarketHours -- Start Of Market Hours
  | startOfSystemHours -- Start Of System Hours
  | auctionCloses -- Auction Closes
  | auctionStarts -- Auction Starts
  | startOfTradingAtLast -- Start Of Trading At Last
  | endOfTradingAtLast -- End Of Trading At Last
  | synchronizedWithGroup -- Synchronized With Group
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .break_ => 0x41
  | .resumptionAfterBreak => 0x42
  | .endOfMessages => 0x43
  | .endOfSystemHours => 0x45
  | .startOfAccepting => 0x49
  | .endOfMarketHours => 0x4D
  | .startOfMessages => 0x4F
  | .startOfMarketHours => 0x51
  | .startOfSystemHours => 0x53
  | .auctionCloses => 0x55
  | .auctionStarts => 0x56
  | .startOfTradingAtLast => 0x54
  | .endOfTradingAtLast => 0x4C
  | .synchronizedWithGroup => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x41 then .break_
  else if byte = 0x42 then .resumptionAfterBreak
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x49 then .startOfAccepting
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x4F then .startOfMessages
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x55 then .auctionCloses
  else if byte = 0x56 then .auctionStarts
  else if byte = 0x54 then .startOfTradingAtLast
  else if byte = 0x4C then .endOfTradingAtLast
  else .synchronizedWithGroup

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | break_ => decide
  | resumptionAfterBreak => decide
  | endOfMessages => decide
  | endOfSystemHours => decide
  | startOfAccepting => decide
  | endOfMarketHours => decide
  | startOfMessages => decide
  | startOfMarketHours => decide
  | startOfSystemHours => decide
  | auctionCloses => decide
  | auctionStarts => decide
  | startOfTradingAtLast => decide
  | endOfTradingAtLast => decide
  | synchronizedWithGroup => decide
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

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56, 0x4D, 0x45, 0x4F, 0x55, 0x51, 0x43, 0x4C, 0x50]

inductive TradingState where
  | trading -- Trading
  | suspended -- Suspended
  | swissAtMidOrderBookSuspended -- Swiss At Mid Order Book Suspended
  | swissEbboOrderBookSuspended -- Swiss Ebbo Order Book Suspended
  | swissEbboAndSwissAtMidOrderBooksSuspended -- Swiss Ebbo And Swiss At Mid Order Books Suspended
  | underlyingCondition -- Underlying Condition
  | quoteOnDemandOrderBookSuspended -- Quote On Demand Order Book Suspended
  | clobSuspendedAndQodOrderBookInTrading -- Clob Suspended And Qod Order Book In Trading
  | lpBidOnlyActive -- Lp Bid Only Active
  | lpBidOnlyActiveAndQodOrderBookSuspended -- Lp Bid Only Active And Qod Order Book Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .trading => 0x54
  | .suspended => 0x56
  | .swissAtMidOrderBookSuspended => 0x4D
  | .swissEbboOrderBookSuspended => 0x45
  | .swissEbboAndSwissAtMidOrderBooksSuspended => 0x4F
  | .underlyingCondition => 0x55
  | .quoteOnDemandOrderBookSuspended => 0x51
  | .clobSuspendedAndQodOrderBookInTrading => 0x43
  | .lpBidOnlyActive => 0x4C
  | .lpBidOnlyActiveAndQodOrderBookSuspended => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .trading
  else if byte = 0x56 then .suspended
  else if byte = 0x4D then .swissAtMidOrderBookSuspended
  else if byte = 0x45 then .swissEbboOrderBookSuspended
  else if byte = 0x4F then .swissEbboAndSwissAtMidOrderBooksSuspended
  else if byte = 0x55 then .underlyingCondition
  else if byte = 0x51 then .quoteOnDemandOrderBookSuspended
  else if byte = 0x43 then .clobSuspendedAndQodOrderBookInTrading
  else if byte = 0x4C then .lpBidOnlyActive
  else .lpBidOnlyActiveAndQodOrderBookSuspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
  | suspended => decide
  | swissAtMidOrderBookSuspended => decide
  | swissEbboOrderBookSuspended => decide
  | swissEbboAndSwissAtMidOrderBooksSuspended => decide
  | underlyingCondition => decide
  | quoteOnDemandOrderBookSuspended => decide
  | clobSuspendedAndQodOrderBookInTrading => decide
  | lpBidOnlyActive => decide
  | lpBidOnlyActiveAndQodOrderBookSuspended => decide
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

/-- Book Condition: one byte code -/
def BookCondition.codes : List UInt8 :=
  [0x44, 0x48, 0x4A, 0x4C, 0x4E, 0x50, 0x31, 0x32, 0x33, 0x34, 0x35]

inductive BookCondition where
  | delayAuction -- Delay Auction
  | stopTrading -- Stop Trading
  | stopTradingWithNonOpening -- Stop Trading With Non Opening
  | delayAuctionWithNonOpening -- Delay Auction With Non Opening
  | normalTrading -- Normal Trading
  | nonOpening -- Non Opening
  | lpBidOnlyReasonUsWithholdingTax -- Lp Bid Only Reason Us Withholding Tax
  | lpBidOnlyReasonIssuerSoldOut -- Lp Bid Only Reason Issuer Sold Out
  | lpBidOnlyReasonIssuerBusinessPolicy -- Lp Bid Only Reason Issuer Business Policy
  | lpBidOnlyReasonSuccessorProduct -- Lp Bid Only Reason Successor Product
  | lpBidOnlyReasonProductWorthless -- Lp Bid Only Reason Product Worthless
  | unlisted (byte : { byte : UInt8 // byte ∉ BookCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BookCondition

def toByte : BookCondition → UInt8
  | .delayAuction => 0x44
  | .stopTrading => 0x48
  | .stopTradingWithNonOpening => 0x4A
  | .delayAuctionWithNonOpening => 0x4C
  | .normalTrading => 0x4E
  | .nonOpening => 0x50
  | .lpBidOnlyReasonUsWithholdingTax => 0x31
  | .lpBidOnlyReasonIssuerSoldOut => 0x32
  | .lpBidOnlyReasonIssuerBusinessPolicy => 0x33
  | .lpBidOnlyReasonSuccessorProduct => 0x34
  | .lpBidOnlyReasonProductWorthless => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BookCondition :=
  if byte = 0x44 then .delayAuction
  else if byte = 0x48 then .stopTrading
  else if byte = 0x4A then .stopTradingWithNonOpening
  else if byte = 0x4C then .delayAuctionWithNonOpening
  else if byte = 0x4E then .normalTrading
  else if byte = 0x50 then .nonOpening
  else if byte = 0x31 then .lpBidOnlyReasonUsWithholdingTax
  else if byte = 0x32 then .lpBidOnlyReasonIssuerSoldOut
  else if byte = 0x33 then .lpBidOnlyReasonIssuerBusinessPolicy
  else if byte = 0x34 then .lpBidOnlyReasonSuccessorProduct
  else .lpBidOnlyReasonProductWorthless

def ofByte (byte : UInt8) : BookCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BookCondition) : ofByte value.toByte = value := by
  cases value with
  | delayAuction => decide
  | stopTrading => decide
  | stopTradingWithNonOpening => decide
  | delayAuctionWithNonOpening => decide
  | normalTrading => decide
  | nonOpening => decide
  | lpBidOnlyReasonUsWithholdingTax => decide
  | lpBidOnlyReasonIssuerSoldOut => decide
  | lpBidOnlyReasonIssuerBusinessPolicy => decide
  | lpBidOnlyReasonSuccessorProduct => decide
  | lpBidOnlyReasonProductWorthless => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BookCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BookCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BookCondition) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BookCondition) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BookCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BookCondition

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | referencePriceUpdate -- Reference Price Update
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .referencePriceUpdate => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .referencePriceUpdate

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | referencePriceUpdate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderVerb) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x43, 0x49, 0x4F]

inductive CrossType where
  | closingAuction -- Closing Auction
  | intradayAuction -- Intraday Auction
  | preOpeningAuction -- Pre Opening Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .closingAuction => 0x43
  | .intradayAuction => 0x49
  | .preOpeningAuction => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x43 then .closingAuction
  else if byte = 0x49 then .intradayAuction
  else .preOpeningAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | closingAuction => decide
  | intradayAuction => decide
  | preOpeningAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CrossType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Debug Packet -/
structure DebugPacket where
  debugText : Capped 65465
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  message.debugText.val

def decode (bytes : List UInt8) : Option DebugPacket := do
  let debugText_ := bytes
  if fits_debugText : debugText_.length ≤ 65465 then
    pure { debugText := ⟨debugText_, fits_debugText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DebugPacket) : (encode message).length ≤ 65465 := by
  have bound_debugText := message.debugText.length_le
  unfold encode
  omega

theorem decode_encode (message : DebugPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.debugText.length_le]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRejectedPacket

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

/-- Quantity Tick Size Message: 16 bytes -/
structure QuantityTickSizeMessage where
  timestamp : BitVec 32
  quantityTickTableId : BitVec 32
  quantityTickSize : BitVec 32
  quantityStart : BitVec 32
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.quantityTickTableId
    ++ (encodeUInt 4 message.quantityTickSize
    ++ (encodeUInt 4 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (quantityTickTableId, bytes) ← decodeUInt 4 bytes
  let (quantityTickSize, bytes) ← decodeUInt 4 bytes
  let (quantityStart, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, quantityTickTableId, quantityTickSize, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 16 := by
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

/-- Price Tick Size Message: 16 bytes -/
structure PriceTickSizeMessage where
  timestamp : BitVec 32
  priceTickTableId : BitVec 32
  priceTickSize : BitVec 32
  priceStart : BitVec 32
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.priceTickTableId
    ++ (encodeUInt 4 message.priceTickSize
    ++ (encodeUInt 4 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (priceTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSize, bytes) ← decodeUInt 4 bytes
  let (priceStart, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, priceTickTableId, priceTickSize, priceStart }, bytes)

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

/-- Orderbook Directory Message: 68 bytes -/
structure OrderbookDirectoryMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  priceType : PriceType
  isin : Alpha 12
  currency : Alpha 3
  group : Alpha 8
  minimumQuantity : BitVec 32
  quantityTickTableId : BitVec 32
  priceTickTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingDate : BitVec 32
  delistingTime : BitVec 32
  qodPriceDecimals : BitVec 32
  securityExchange : Alpha 4
  referenceExchange : Alpha 4
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (PriceType.encode message.priceType
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 4 message.minimumQuantity
    ++ (encodeUInt 4 message.quantityTickTableId
    ++ (encodeUInt 4 message.priceTickTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (encodeUInt 4 message.qodPriceDecimals
    ++ (Alpha.encode message.securityExchange
    ++ (Alpha.encode message.referenceExchange))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 4 bytes
  let (quantityTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (qodPriceDecimals, bytes) ← decodeUInt 4 bytes
  let (securityExchange, bytes) ← Alpha.decode 4 bytes
  let (referenceExchange, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, orderbook, priceType, isin, currency, group, minimumQuantity, quantityTickTableId, priceTickTableId, priceDecimals, delistingDate, delistingTime, qodPriceDecimals, securityExchange, referenceExchange }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  timestamp : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  bookCondition : BookCondition
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (BookCondition.encode message.bookCondition)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (bookCondition, bytes) ← BookCondition.decode bytes
  pure ({ timestamp, orderbook, tradingState, bookCondition }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, BookCondition.encode_length]

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
  rw [BookCondition.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Add Order Message: 25 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 32
  orderNumber : BitVec 64
  orderVerb : OrderVerb
  orderQuantity : BitVec 32
  orderbook : BitVec 32
  orderPrice : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 4 message.orderQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.orderPrice)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (orderQuantity, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (orderPrice, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, orderNumber, orderVerb, orderQuantity, orderbook, orderPrice }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Indicative Price Quantity Message: 29 bytes -/
structure IndicativePriceQuantityMessage where
  timestamp : BitVec 32
  theoreticalOpeningQuantity : BitVec 64
  orderbook : BitVec 32
  bestBid : BitVec 32
  bestOffer : BitVec 32
  theoreticalOpeningPrice : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace IndicativePriceQuantityMessage

def encode (message : IndicativePriceQuantityMessage) : List UInt8 :=
  encodeUInt 4 message.timestamp
    ++ (encodeUInt 8 message.theoreticalOpeningQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.bestBid
    ++ (encodeUInt 4 message.bestOffer
    ++ (encodeUInt 4 message.theoreticalOpeningPrice
    ++ (CrossType.encode message.crossType))))))

def decode (bytes : List UInt8) : Option (IndicativePriceQuantityMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBid, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ timestamp, theoreticalOpeningQuantity, orderbook, bestBid, bestOffer, theoreticalOpeningPrice, crossType }, bytes)

@[simp] theorem encode_length (message : IndicativePriceQuantityMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : IndicativePriceQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceQuantityMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end IndicativePriceQuantityMessage

/-- Glimpse Snapshot Message: 8 bytes -/
structure GlimpseSnapshotMessage where
  sequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace GlimpseSnapshotMessage

def encode (message : GlimpseSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.sequenceNumber

def decode (bytes : List UInt8) : Option (GlimpseSnapshotMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : GlimpseSnapshotMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : GlimpseSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlimpseSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end GlimpseSnapshotMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- "T" 0x54
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- "M" 0x4D
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- "L" 0x4C
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- "R" 0x52
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | indicativePriceQuantityMessage (message : IndicativePriceQuantityMessage) -- "I" 0x49
  | glimpseSnapshotMessage (message : GlimpseSnapshotMessage) -- "G" 0x47
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .quantityTickSizeMessage _ => 77
  | .priceTickSizeMessage _ => 76
  | .orderbookDirectoryMessage _ => 82
  | .orderbookTradingActionMessage _ => 72
  | .addOrderMessage _ => 65
  | .indicativePriceQuantityMessage _ => 73
  | .glimpseSnapshotMessage _ => 71

def encode : SequencedMessage → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .indicativePriceQuantityMessage message => IndicativePriceQuantityMessage.encode message
  | .glimpseSnapshotMessage message => GlimpseSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 68 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [encode, IndicativePriceQuantityMessage.encode_length]
    omega
  | glimpseSnapshotMessage inner =>
    simp only [encode, GlimpseSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 73 then (IndicativePriceQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceQuantityMessage message, rest)
  else if tag = 71 then (GlimpseSnapshotMessage.decode bytes).map fun (message, rest) => (.glimpseSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 69 := by
  unfold encode
  cases message.sequencedMessage with
  | timeStampSecondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, IndicativePriceQuantityMessage.encode_length]
    omega
  | glimpseSnapshotMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, GlimpseSnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : ServerPayload → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65465 := by
  cases message with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 43 then (DebugPacket.decode bytes).map fun message => .debugPacket message
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedPacket message) else none
  else if tag = 74 then (LoginRejectedPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedPacket message) else none
  else if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 72 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 90 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode]
  | loginAcceptedPacket message => simp [decode, encode, tag, LoginAcceptedPacket.decode_encode_nil]
  | loginRejectedPacket message => simp [decode, encode, tag, LoginRejectedPacket.decode_encode_nil]
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerSoupBinTcpPacket := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let serverPayload ← ServerPayload.decode serverPacketType bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    have bound_inner := DebugPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramedAll 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : ServerSoupBinTcpPacket) : Bool :=
  ServerPayload.endsSession message.serverPayload

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  serverSoupBinTcpPacket_last : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  if last_serverSoupBinTcpPacket : endsLast ServerSoupBinTcpPacket.endsSession serverSoupBinTcpPacket = true then
    pure { serverSoupBinTcpPacket, serverSoupBinTcpPacket_last := last_serverSoupBinTcpPacket }
  else none

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rw [dite_eq_left message.serverSoupBinTcpPacket_last]
  rfl

end ServerPacket

end Omi.SixSixswissexchangeSnapshotGlimpseV1240Server
