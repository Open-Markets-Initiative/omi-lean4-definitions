import Wire

/-!
# TMX Group Level 1 v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxalphaLevel1QrtmdV21

/-- Retransmission Identifier: one byte code -/
def RetransmissionIdentifier.codes : List UInt8 :=
  [0x30]

inductive RetransmissionIdentifier where
  | normalTransmission -- Normal Transmission
  | unlisted (byte : { byte : UInt8 // byte ∉ RetransmissionIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RetransmissionIdentifier

def toByte : RetransmissionIdentifier → UInt8
  | .normalTransmission => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : RetransmissionIdentifier :=
  .normalTransmission

def ofByte (byte : UInt8) : RetransmissionIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RetransmissionIdentifier) : ofByte value.toByte = value := by
  cases value with
  | normalTransmission => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RetransmissionIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RetransmissionIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RetransmissionIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RetransmissionIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RetransmissionIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RetransmissionIdentifier

/-- Continuation Identifier: one byte code -/
def ContinuationIdentifier.codes : List UInt8 :=
  [0x30]

inductive ContinuationIdentifier where
  | standAloneMessage -- Stand Alone Message
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinuationIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinuationIdentifier

def toByte : ContinuationIdentifier → UInt8
  | .standAloneMessage => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ContinuationIdentifier :=
  .standAloneMessage

def ofByte (byte : UInt8) : ContinuationIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinuationIdentifier) : ofByte value.toByte = value := by
  cases value with
  | standAloneMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinuationIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinuationIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinuationIdentifier) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContinuationIdentifier) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContinuationIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinuationIdentifier

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x49, 0x42, 0x43, 0x44, 0x52, 0x56, 0x20]

inductive CrossType where
  | internal -- Internal
  | basis -- Basis
  | contingent -- Contingent
  | derivativeRelated -- Derivative Related
  | regular -- Regular
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | default -- Default
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .internal => 0x49
  | .basis => 0x42
  | .contingent => 0x43
  | .derivativeRelated => 0x44
  | .regular => 0x52
  | .volumeWeightedAveragePrice => 0x56
  | .default => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x49 then .internal
  else if byte = 0x42 then .basis
  else if byte = 0x43 then .contingent
  else if byte = 0x44 then .derivativeRelated
  else if byte = 0x52 then .regular
  else if byte = 0x56 then .volumeWeightedAveragePrice
  else .default

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | internal => decide
  | basis => decide
  | contingent => decide
  | derivativeRelated => decide
  | regular => decide
  | volumeWeightedAveragePrice => decide
  | default => decide
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

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Bypass where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Bypass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Bypass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Bypass) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Bypass) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Bypass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Bypass

/-- Opening Trade: one byte code -/
def OpeningTrade.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OpeningTrade where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ OpeningTrade.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpeningTrade

def toByte : OpeningTrade → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpeningTrade :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : OpeningTrade :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpeningTrade) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpeningTrade) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpeningTrade × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpeningTrade) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpeningTrade) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpeningTrade) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpeningTrade

/-- Settlement Terms: one byte code -/
def SettlementTerms.codes : List UInt8 :=
  [0x20, 0x43, 0x4E, 0x4D, 0x54, 0x44]

inductive SettlementTerms where
  | default -- Default
  | cash -- Cash
  | nonNet -- Non Net
  | derivativesRelatedContingentEquityTrade -- Derivatives Related Contingent Equity Trade
  | cashToday -- Cash Today
  | settlementDate -- Settlement Date
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementTerms.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementTerms

def toByte : SettlementTerms → UInt8
  | .default => 0x20
  | .cash => 0x43
  | .nonNet => 0x4E
  | .derivativesRelatedContingentEquityTrade => 0x4D
  | .cashToday => 0x54
  | .settlementDate => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementTerms :=
  if byte = 0x20 then .default
  else if byte = 0x43 then .cash
  else if byte = 0x4E then .nonNet
  else if byte = 0x4D then .derivativesRelatedContingentEquityTrade
  else if byte = 0x54 then .cashToday
  else .settlementDate

def ofByte (byte : UInt8) : SettlementTerms :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementTerms) : ofByte value.toByte = value := by
  cases value with
  | default => decide
  | cash => decide
  | nonNet => decide
  | derivativesRelatedContingentEquityTrade => decide
  | cashToday => decide
  | settlementDate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementTerms) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementTerms × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementTerms) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementTerms) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementTerms) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementTerms

/-- Is Dark: one byte code -/
def IsDark.codes : List UInt8 :=
  [0x4E]

inductive IsDark where
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ IsDark.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IsDark

def toByte : IsDark → UInt8
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : IsDark :=
  .no

def ofByte (byte : UInt8) : IsDark :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IsDark) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IsDark) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IsDark × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IsDark) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IsDark) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IsDark) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IsDark

/-- Product Type: one byte code -/
def ProductType.codes : List UInt8 :=
  [0x42, 0x45, 0x4D, 0x46]

inductive ProductType where
  | debenture -- Debenture
  | equity -- Equity
  | mutualFund -- Mutual Fund
  | etf -- Etf
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductType

def toByte : ProductType → UInt8
  | .debenture => 0x42
  | .equity => 0x45
  | .mutualFund => 0x4D
  | .etf => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductType :=
  if byte = 0x42 then .debenture
  else if byte = 0x45 then .equity
  else if byte = 0x4D then .mutualFund
  else .etf

def ofByte (byte : UInt8) : ProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductType) : ofByte value.toByte = value := by
  cases value with
  | debenture => decide
  | equity => decide
  | mutualFund => decide
  | etf => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProductType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProductType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProductType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ProductType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ProductType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProductType

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56]

inductive ListingMarket where
  | tsx -- Tsx
  | tsxv -- Tsxv
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .tsxv => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else .tsxv

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxv => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ListingMarket) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- Test Symbol: one byte code -/
def TestSymbol.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSymbol where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSymbol.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSymbol

def toByte : TestSymbol → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSymbol :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSymbol :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSymbol) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSymbol) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSymbol × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSymbol) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TestSymbol) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TestSymbol) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSymbol

/-- Bulletin Indicator: one byte code -/
def BulletinIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive BulletinIndicator where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ BulletinIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BulletinIndicator

def toByte : BulletinIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BulletinIndicator :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : BulletinIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BulletinIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BulletinIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BulletinIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BulletinIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BulletinIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BulletinIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BulletinIndicator

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x50, 0x4F, 0x53, 0x43, 0x46, 0x4E]

inductive MarketState where
  | preOpen -- Pre Open
  | opening -- Opening
  | open_ -- Open
  | closed -- Closed
  | extendedHoursClose -- Extended Hours Close
  | extendedHoursCxls -- Extended Hours Cxls
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preOpen => 0x50
  | .opening => 0x4F
  | .open_ => 0x53
  | .closed => 0x43
  | .extendedHoursClose => 0x46
  | .extendedHoursCxls => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preOpen
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .open_
  else if byte = 0x43 then .closed
  else if byte = 0x46 then .extendedHoursClose
  else .extendedHoursCxls

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preOpen => decide
  | opening => decide
  | open_ => decide
  | closed => decide
  | extendedHoursClose => decide
  | extendedHoursCxls => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketState) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MarketState) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MarketState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketState

/-- Trade Message: 92 bytes -/
structure TradeMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  lastSale : Alpha 11
  tradeId : Alpha 9
  crossType : CrossType
  bypass : Bypass
  openingTrade : OpeningTrade
  settlementTerms : SettlementTerms
  isDark : IsDark
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradeId
    ++ (CrossType.encode message.crossType
    ++ (Bypass.encode message.bypass
    ++ (OpeningTrade.encode message.openingTrade
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (IsDark.encode message.isDark
    ++ (Alpha.encode message.tradingSystemTimeStamp)))))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← Alpha.decode 9 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (openingTrade, bytes) ← OpeningTrade.decode bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (isDark, bytes) ← IsDark.decode bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, lastSale, tradeId, crossType, bypass, openingTrade, settlementTerms, isDark, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CrossType.encode_length, Bypass.encode_length, OpeningTrade.encode_length, SettlementTerms.encode_length, IsDark.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsDark.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Symbol Status Message: 136 bytes -/
structure SymbolStatusMessage where
  symbol : Alpha 12
  tradingSystemTimeStamp : Alpha 23
  exchangeId : Alpha 3
  cusip : Alpha 12
  boardLot : Alpha 9
  currency : Alpha 1
  faceValue : Alpha 9
  lastSale : Alpha 11
  productType : ProductType
  symbolName : Alpha 40
  stockGroup : Alpha 2
  stockState : Alpha 2
  listingMarket : ListingMarket
  minPoQty : Alpha 9
  testSymbol : TestSymbol
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.exchangeId
    ++ (Alpha.encode message.cusip
    ++ (Alpha.encode message.boardLot
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.faceValue
    ++ (Alpha.encode message.lastSale
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.symbolName
    ++ (Alpha.encode message.stockGroup
    ++ (Alpha.encode message.stockState
    ++ (ListingMarket.encode message.listingMarket
    ++ (Alpha.encode message.minPoQty
    ++ (TestSymbol.encode message.testSymbol))))))))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (exchangeId, bytes) ← Alpha.decode 3 bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (boardLot, bytes) ← Alpha.decode 9 bytes
  let (currency, bytes) ← Alpha.decode 1 bytes
  let (faceValue, bytes) ← Alpha.decode 9 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (symbolName, bytes) ← Alpha.decode 40 bytes
  let (stockGroup, bytes) ← Alpha.decode 2 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (minPoQty, bytes) ← Alpha.decode 9 bytes
  let (testSymbol, bytes) ← TestSymbol.decode bytes
  pure ({ symbol, tradingSystemTimeStamp, exchangeId, cusip, boardLot, currency, faceValue, lastSale, productType, symbolName, stockGroup, stockState, listingMarket, minPoQty, testSymbol }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 136 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ProductType.encode_length, ListingMarket.encode_length, TestSymbol.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TestSymbol.decode_encode, some_bind]
  rfl

end SymbolStatusMessage

/-- Stock State Message: 83 bytes -/
structure StockStateMessage where
  symbol : Alpha 12
  tradingSystemTimeStamp : Alpha 23
  comment : Alpha 40
  stockState : Alpha 2
  openingTime : Alpha 6
  deriving DecidableEq, Repr

namespace StockStateMessage

def encode (message : StockStateMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.comment
    ++ (Alpha.encode message.stockState
    ++ (Alpha.encode message.openingTime))))

def decode (bytes : List UInt8) : Option (StockStateMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (comment, bytes) ← Alpha.decode 40 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (openingTime, bytes) ← Alpha.decode 6 bytes
  pure ({ symbol, tradingSystemTimeStamp, comment, stockState, openingTime }, bytes)

@[simp] theorem encode_length (message : StockStateMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : StockStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StockStateMessage

/-- Quote Message: 71 bytes -/
structure QuoteMessage where
  symbol : Alpha 12
  bidPrice : Alpha 9
  bidSize : Alpha 9
  askPrice : Alpha 9
  askSize : Alpha 9
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace QuoteMessage

def encode (message : QuoteMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.bidPrice
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.askPrice
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.tradingSystemTimeStamp)))))

def decode (bytes : List UInt8) : Option (QuoteMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (bidPrice, bytes) ← Alpha.decode 9 bytes
  let (bidSize, bytes) ← Alpha.decode 9 bytes
  let (askPrice, bytes) ← Alpha.decode 9 bytes
  let (askSize, bytes) ← Alpha.decode 9 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, bidPrice, bidSize, askPrice, askSize, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : QuoteMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : QuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteMessage

/-- General Message: 104 bytes -/
structure GeneralMessage where
  tradingSystemTimeStamp : Alpha 23
  bulletinIndicator : BulletinIndicator
  messageText : Alpha 80
  deriving DecidableEq, Repr

namespace GeneralMessage

def encode (message : GeneralMessage) : List UInt8 :=
  Alpha.encode message.tradingSystemTimeStamp
    ++ (BulletinIndicator.encode message.bulletinIndicator
    ++ (Alpha.encode message.messageText))

def decode (bytes : List UInt8) : Option (GeneralMessage × List UInt8) := do
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (bulletinIndicator, bytes) ← BulletinIndicator.decode bytes
  let (messageText, bytes) ← Alpha.decode 80 bytes
  pure ({ tradingSystemTimeStamp, bulletinIndicator, messageText }, bytes)

@[simp] theorem encode_length (message : GeneralMessage) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BulletinIndicator.encode_length]

theorem encode_length_pos (message : GeneralMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GeneralMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BulletinIndicator.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GeneralMessage

/-- Trade Cancellation Message: 87 bytes -/
structure TradeCancellationMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  originalTradeId : Alpha 9
  lastSale : Alpha 11
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.originalTradeId
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradingSystemTimeStamp))))))))

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (originalTradeId, bytes) ← Alpha.decode 9 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, originalTradeId, lastSale, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancellationMessage

/-- Market State Message: 26 bytes -/
structure MarketStateMessage where
  tradingSystemTimeStamp : Alpha 23
  stockGroup : Alpha 2
  marketState : MarketState
  deriving DecidableEq, Repr

namespace MarketStateMessage

def encode (message : MarketStateMessage) : List UInt8 :=
  Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.stockGroup
    ++ (MarketState.encode message.marketState))

def decode (bytes : List UInt8) : Option (MarketStateMessage × List UInt8) := do
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (stockGroup, bytes) ← Alpha.decode 2 bytes
  let (marketState, bytes) ← MarketState.decode bytes
  pure ({ tradingSystemTimeStamp, stockGroup, marketState }, bytes)

@[simp] theorem encode_length (message : MarketStateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, MarketState.encode_length]

theorem encode_length_pos (message : MarketStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [MarketState.decode_encode, some_bind]
  rfl

end MarketStateMessage

/-- Trading Tier Status Message: 40 bytes -/
structure TradingTierStatusMessage where
  exchangeId : Alpha 3
  totalNumberOfSymbols : Alpha 5
  totalNumberOfStockGroups : Alpha 3
  tradingSystemTimeStamp : Alpha 23
  tradingTierId : Alpha 6
  deriving DecidableEq, Repr

namespace TradingTierStatusMessage

def encode (message : TradingTierStatusMessage) : List UInt8 :=
  Alpha.encode message.exchangeId
    ++ (Alpha.encode message.totalNumberOfSymbols
    ++ (Alpha.encode message.totalNumberOfStockGroups
    ++ (Alpha.encode message.tradingSystemTimeStamp
    ++ (Alpha.encode message.tradingTierId))))

def decode (bytes : List UInt8) : Option (TradingTierStatusMessage × List UInt8) := do
  let (exchangeId, bytes) ← Alpha.decode 3 bytes
  let (totalNumberOfSymbols, bytes) ← Alpha.decode 5 bytes
  let (totalNumberOfStockGroups, bytes) ← Alpha.decode 3 bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  let (tradingTierId, bytes) ← Alpha.decode 6 bytes
  pure ({ exchangeId, totalNumberOfSymbols, totalNumberOfStockGroups, tradingSystemTimeStamp, tradingTierId }, bytes)

@[simp] theorem encode_length (message : TradingTierStatusMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TradingTierStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingTierStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingTierStatusMessage

/-- Trade Correction Message: 101 bytes -/
structure TradeCorrectionMessage where
  symbol : Alpha 12
  volume : Alpha 9
  tradePrice : Alpha 11
  buyerId : Alpha 3
  sellerId : Alpha 3
  tradeTimeStamp : Alpha 6
  lastSale : Alpha 11
  tradeId : Alpha 9
  crossType : CrossType
  bypass : Bypass
  openingTrade : OpeningTrade
  settlementTerms : SettlementTerms
  originalTradeId : Alpha 9
  isDark : IsDark
  tradingSystemTimeStamp : Alpha 23
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.buyerId
    ++ (Alpha.encode message.sellerId
    ++ (Alpha.encode message.tradeTimeStamp
    ++ (Alpha.encode message.lastSale
    ++ (Alpha.encode message.tradeId
    ++ (CrossType.encode message.crossType
    ++ (Bypass.encode message.bypass
    ++ (OpeningTrade.encode message.openingTrade
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (Alpha.encode message.originalTradeId
    ++ (IsDark.encode message.isDark
    ++ (Alpha.encode message.tradingSystemTimeStamp))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (volume, bytes) ← Alpha.decode 9 bytes
  let (tradePrice, bytes) ← Alpha.decode 11 bytes
  let (buyerId, bytes) ← Alpha.decode 3 bytes
  let (sellerId, bytes) ← Alpha.decode 3 bytes
  let (tradeTimeStamp, bytes) ← Alpha.decode 6 bytes
  let (lastSale, bytes) ← Alpha.decode 11 bytes
  let (tradeId, bytes) ← Alpha.decode 9 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (openingTrade, bytes) ← OpeningTrade.decode bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (originalTradeId, bytes) ← Alpha.decode 9 bytes
  let (isDark, bytes) ← IsDark.decode bytes
  let (tradingSystemTimeStamp, bytes) ← Alpha.decode 23 bytes
  pure ({ symbol, volume, tradePrice, buyerId, sellerId, tradeTimeStamp, lastSale, tradeId, crossType, bypass, openingTrade, settlementTerms, originalTradeId, isDark, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, CrossType.encode_length, Bypass.encode_length, OpeningTrade.encode_length, SettlementTerms.encode_length, IsDark.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningTrade.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, IsDark.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCorrectionMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | tradeMessage (message : TradeMessage) -- "A " 0x4120
  | symbolStatusMessage (message : SymbolStatusMessage) -- "B " 0x4220
  | stockStateMessage (message : StockStateMessage) -- "D " 0x4420
  | quoteMessage (message : QuoteMessage) -- "E " 0x4520
  | generalMessage (message : GeneralMessage) -- "G " 0x4720
  | tradeCancellationMessage (message : TradeCancellationMessage) -- "H " 0x4820
  | marketStateMessage (message : MarketStateMessage) -- "S " 0x5320
  | tradingTierStatusMessage (message : TradingTierStatusMessage) -- "T " 0x5420
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "X " 0x5820
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .tradeMessage _ => 16672
  | .symbolStatusMessage _ => 16928
  | .stockStateMessage _ => 17440
  | .quoteMessage _ => 17696
  | .generalMessage _ => 18208
  | .tradeCancellationMessage _ => 18464
  | .marketStateMessage _ => 21280
  | .tradingTierStatusMessage _ => 21536
  | .tradeCorrectionMessage _ => 22560

def encode : MessageBody → List UInt8
  | .tradeMessage message => TradeMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .stockStateMessage message => StockStateMessage.encode message
  | .quoteMessage message => QuoteMessage.encode message
  | .generalMessage message => GeneralMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .marketStateMessage message => MarketStateMessage.encode message
  | .tradingTierStatusMessage message => TradingTierStatusMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 136 := by
  cases message with
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | stockStateMessage inner =>
    simp only [encode, StockStateMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [encode, QuoteMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [encode, GeneralMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | marketStateMessage inner =>
    simp only [encode, MarketStateMessage.encode_length]
    omega
  | tradingTierStatusMessage inner =>
    simp only [encode, TradingTierStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 16672 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 16928 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 17440 then (StockStateMessage.decode bytes).map fun (message, rest) => (.stockStateMessage message, rest)
  else if tag = 17696 then (QuoteMessage.decode bytes).map fun (message, rest) => (.quoteMessage message, rest)
  else if tag = 18208 then (GeneralMessage.decode bytes).map fun (message, rest) => (.generalMessage message, rest)
  else if tag = 18464 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 21280 then (MarketStateMessage.decode bytes).map fun (message, rest) => (.marketStateMessage message, rest)
  else if tag = 21536 then (TradingTierStatusMessage.decode bytes).map fun (message, rest) => (.tradingTierStatusMessage message, rest)
  else if tag = 22560 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Packet -/
structure Packet where
  qrtmdStx : BitVec 8
  messageLength : Alpha 4
  sequenceNumber : Alpha 9
  serviceIdentifier : Alpha 3
  retransmissionIdentifier : RetransmissionIdentifier
  continuationIdentifier : ContinuationIdentifier
  exchangeIdentifier : Alpha 2
  messageBody : MessageBody
  qrtmdEtx : BitVec 8
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.qrtmdStx
    ++ (Alpha.encode message.messageLength
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.serviceIdentifier
    ++ (RetransmissionIdentifier.encode message.retransmissionIdentifier
    ++ (ContinuationIdentifier.encode message.continuationIdentifier
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (Alpha.encode message.exchangeIdentifier
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.qrtmdEtx)))))))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (qrtmdStx, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← Alpha.decode 4 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (serviceIdentifier, bytes) ← Alpha.decode 3 bytes
  let (retransmissionIdentifier, bytes) ← RetransmissionIdentifier.decode bytes
  let (continuationIdentifier, bytes) ← ContinuationIdentifier.decode bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (exchangeIdentifier, bytes) ← Alpha.decode 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (qrtmdEtx, bytes) ← decodeUInt 1 bytes
  pure ({ qrtmdStx, messageLength, sequenceNumber, serviceIdentifier, retransmissionIdentifier, continuationIdentifier, exchangeIdentifier, messageBody, qrtmdEtx }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 160 := by
  unfold encode
  cases message.messageBody with
  | tradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, SymbolStatusMessage.encode_length]
    omega
  | stockStateMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, StockStateMessage.encode_length]
    omega
  | quoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, QuoteMessage.encode_length]
    omega
  | generalMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, GeneralMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeCancellationMessage.encode_length]
    omega
  | marketStateMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, MarketStateMessage.encode_length]
    omega
  | tradingTierStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradingTierStatusMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, RetransmissionIdentifier.encode_length, ContinuationIdentifier.encode_length, TradeCorrectionMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RetransmissionIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContinuationIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Packet

end Omi.TmxTsxalphaLevel1QrtmdV21
