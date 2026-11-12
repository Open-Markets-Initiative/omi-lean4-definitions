import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Product 29 v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataProduct29IntraV11

/-- Origin: one byte code -/
def Origin.codes : List UInt8 :=
  [0x4D, 0x49, 0x41]

inductive Origin where
  | bmv -- Bmv
  | biva -- Biva
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ Origin.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Origin

def toByte : Origin → UInt8
  | .bmv => 0x4D
  | .biva => 0x49
  | .both => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Origin :=
  if byte = 0x4D then .bmv
  else if byte = 0x49 then .biva
  else .both

def ofByte (byte : UInt8) : Origin :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Origin) : ofByte value.toByte = value := by
  cases value with
  | bmv => decide
  | biva => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Origin) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Origin × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Origin) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Origin) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Origin) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Origin

/-- Direction Of The Bid: one byte code -/
def DirectionOfTheBid.codes : List UInt8 :=
  [0x43, 0x56]

inductive DirectionOfTheBid where
  | purchase -- Purchase
  | sale -- Sale
  | unlisted (byte : { byte : UInt8 // byte ∉ DirectionOfTheBid.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DirectionOfTheBid

def toByte : DirectionOfTheBid → UInt8
  | .purchase => 0x43
  | .sale => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DirectionOfTheBid :=
  if byte = 0x43 then .purchase
  else .sale

def ofByte (byte : UInt8) : DirectionOfTheBid :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DirectionOfTheBid) : ofByte value.toByte = value := by
  cases value with
  | purchase => decide
  | sale => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DirectionOfTheBid) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DirectionOfTheBid × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DirectionOfTheBid) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DirectionOfTheBid) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DirectionOfTheBid) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DirectionOfTheBid

/-- Type Of Trading: one byte code -/
def TypeOfTrading.codes : List UInt8 :=
  [0x45, 0x43, 0x42, 0x44, 0x57]

inductive TypeOfTrading where
  | continuousElectronicTrading -- Continuous Electronic Trading
  | marketOnClose -- Market On Close
  | blockTrading -- Block Trading
  | debtTrading -- Debt Trading
  | warrantsTrading -- Warrants Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfTrading.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfTrading

def toByte : TypeOfTrading → UInt8
  | .continuousElectronicTrading => 0x45
  | .marketOnClose => 0x43
  | .blockTrading => 0x42
  | .debtTrading => 0x44
  | .warrantsTrading => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfTrading :=
  if byte = 0x45 then .continuousElectronicTrading
  else if byte = 0x43 then .marketOnClose
  else if byte = 0x42 then .blockTrading
  else if byte = 0x44 then .debtTrading
  else .warrantsTrading

def ofByte (byte : UInt8) : TypeOfTrading :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfTrading) : ofByte value.toByte = value := by
  cases value with
  | continuousElectronicTrading => decide
  | marketOnClose => decide
  | blockTrading => decide
  | debtTrading => decide
  | warrantsTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfTrading) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfTrading × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfTrading) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfTrading) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfTrading) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfTrading

/-- Market: one byte code -/
def Market.codes : List UInt8 :=
  [0x4C, 0x47, 0x54, 0x46]

inductive Market where
  | local_ -- Local
  | global -- Global
  | etFs -- Et Fs
  | reiTs -- Rei Ts
  | unlisted (byte : { byte : UInt8 // byte ∉ Market.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Market

def toByte : Market → UInt8
  | .local_ => 0x4C
  | .global => 0x47
  | .etFs => 0x54
  | .reiTs => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Market :=
  if byte = 0x4C then .local_
  else if byte = 0x47 then .global
  else if byte = 0x54 then .etFs
  else .reiTs

def ofByte (byte : UInt8) : Market :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Market) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | global => decide
  | etFs => decide
  | reiTs => decide
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

/-- Last Quote Message: 23 bytes -/
structure LastQuoteMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  volume : BitVec 64
  priceRate : BitVec 64
  directionOfTheBid : DirectionOfTheBid
  typeOfTrading : TypeOfTrading
  deriving DecidableEq, Repr

namespace LastQuoteMessage

def encode (message : LastQuoteMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.volume
    ++ (encodeUInt 8 message.priceRate
    ++ (DirectionOfTheBid.encode message.directionOfTheBid
    ++ (TypeOfTrading.encode message.typeOfTrading)))))

def decode (bytes : List UInt8) : Option (LastQuoteMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (volume, bytes) ← decodeUInt 8 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (directionOfTheBid, bytes) ← DirectionOfTheBid.decode bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  pure ({ instrumentNumber, origin, volume, priceRate, directionOfTheBid, typeOfTrading }, bytes)

@[simp] theorem encode_length (message : LastQuoteMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, DirectionOfTheBid.encode_length, TypeOfTrading.encode_length]

theorem encode_length_pos (message : LastQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DirectionOfTheBid.decode_encode, some_bind]
  dsimp only
  rw [TypeOfTrading.decode_encode, some_bind]
  rfl

end LastQuoteMessage

/-- Benchmark Trade Message: 25 bytes -/
structure BenchmarkTradeMessage where
  origin : Origin
  averageVolume : BitVec 64
  averageTradedValue : BitVec 64
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace BenchmarkTradeMessage

def encode (message : BenchmarkTradeMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 8 message.averageVolume
    ++ (encodeUInt 8 message.averageTradedValue
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))

def decode (bytes : List UInt8) : Option (BenchmarkTradeMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (averageVolume, bytes) ← decodeUInt 8 bytes
  let (averageTradedValue, bytes) ← decodeUInt 8 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, averageVolume, averageTradedValue, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : BenchmarkTradeMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BenchmarkTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BenchmarkTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BenchmarkTradeMessage

/-- Price Leaderboard Message: 33 bytes -/
structure PriceLeaderboardMessage where
  origin : Origin
  tBestBid : BitVec 32
  tTieBestBid : BitVec 32
  tWithoutBestBid : BitVec 32
  tBestAsk : BitVec 32
  tTieBestAsk : BitVec 32
  tWithoutBestAsk : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace PriceLeaderboardMessage

def encode (message : PriceLeaderboardMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 4 message.tBestBid
    ++ (encodeUInt 4 message.tTieBestBid
    ++ (encodeUInt 4 message.tWithoutBestBid
    ++ (encodeUInt 4 message.tBestAsk
    ++ (encodeUInt 4 message.tTieBestAsk
    ++ (encodeUInt 4 message.tWithoutBestAsk
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))))))

def decode (bytes : List UInt8) : Option (PriceLeaderboardMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (tBestBid, bytes) ← decodeUInt 4 bytes
  let (tTieBestBid, bytes) ← decodeUInt 4 bytes
  let (tWithoutBestBid, bytes) ← decodeUInt 4 bytes
  let (tBestAsk, bytes) ← decodeUInt 4 bytes
  let (tTieBestAsk, bytes) ← decodeUInt 4 bytes
  let (tWithoutBestAsk, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, tBestBid, tTieBestBid, tWithoutBestBid, tBestAsk, tTieBestAsk, tWithoutBestAsk, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : PriceLeaderboardMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : PriceLeaderboardMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLeaderboardMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PriceLeaderboardMessage

/-- Trading Sniper Message: 73 bytes -/
structure TradingSniperMessage where
  origin : Origin
  depthBid : BitVec 64
  depthAsk : BitVec 64
  depthBid10L : BitVec 64
  depthAsk10L : BitVec 64
  vwpBid10L : BitVec 64
  vwpAsk10L : BitVec 64
  vwpBid : BitVec 64
  vwpAsk : BitVec 64
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace TradingSniperMessage

def encode (message : TradingSniperMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 8 message.depthBid
    ++ (encodeUInt 8 message.depthAsk
    ++ (encodeUInt 8 message.depthBid10L
    ++ (encodeUInt 8 message.depthAsk10L
    ++ (encodeUInt 8 message.vwpBid10L
    ++ (encodeUInt 8 message.vwpAsk10L
    ++ (encodeUInt 8 message.vwpBid
    ++ (encodeUInt 8 message.vwpAsk
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))))))))

def decode (bytes : List UInt8) : Option (TradingSniperMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (depthBid, bytes) ← decodeUInt 8 bytes
  let (depthAsk, bytes) ← decodeUInt 8 bytes
  let (depthBid10L, bytes) ← decodeUInt 8 bytes
  let (depthAsk10L, bytes) ← decodeUInt 8 bytes
  let (vwpBid10L, bytes) ← decodeUInt 8 bytes
  let (vwpAsk10L, bytes) ← decodeUInt 8 bytes
  let (vwpBid, bytes) ← decodeUInt 8 bytes
  let (vwpAsk, bytes) ← decodeUInt 8 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, depthBid, depthAsk, depthBid10L, depthAsk10L, vwpBid10L, vwpAsk10L, vwpBid, vwpAsk, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : TradingSniperMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingSniperMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSniperMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradingSniperMessage

/-- Depth At Best Prices Message: 25 bytes -/
structure DepthAtBestPricesMessage where
  origin : Origin
  instrumentsBb : BitVec 16
  instrumentsGvBb : BitVec 16
  ratioVAtBb : BitVec 32
  instrumentsBa : BitVec 16
  instrumentsGvBa : BitVec 16
  ratioVAtBa : BitVec 32
  market : Market
  sector : BitVec 8
  instrumentNumber : BitVec 32
  indices : Alpha 2
  deriving DecidableEq, Repr

namespace DepthAtBestPricesMessage

def encode (message : DepthAtBestPricesMessage) : List UInt8 :=
  Origin.encode message.origin
    ++ (encodeUInt 2 message.instrumentsBb
    ++ (encodeUInt 2 message.instrumentsGvBb
    ++ (encodeUInt 4 message.ratioVAtBb
    ++ (encodeUInt 2 message.instrumentsBa
    ++ (encodeUInt 2 message.instrumentsGvBa
    ++ (encodeUInt 4 message.ratioVAtBa
    ++ (Market.encode message.market
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.indices))))))))))

def decode (bytes : List UInt8) : Option (DepthAtBestPricesMessage × List UInt8) := do
  let (origin, bytes) ← Origin.decode bytes
  let (instrumentsBb, bytes) ← decodeUInt 2 bytes
  let (instrumentsGvBb, bytes) ← decodeUInt 2 bytes
  let (ratioVAtBb, bytes) ← decodeUInt 4 bytes
  let (instrumentsBa, bytes) ← decodeUInt 2 bytes
  let (instrumentsGvBa, bytes) ← decodeUInt 2 bytes
  let (ratioVAtBa, bytes) ← decodeUInt 4 bytes
  let (market, bytes) ← Market.decode bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (indices, bytes) ← Alpha.decode 2 bytes
  pure ({ origin, instrumentsBb, instrumentsGvBb, ratioVAtBb, instrumentsBa, instrumentsGvBa, ratioVAtBa, market, sector, instrumentNumber, indices }, bytes)

@[simp] theorem encode_length (message : DepthAtBestPricesMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Origin.encode_length, encodeUInt_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : DepthAtBestPricesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DepthAtBestPricesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DepthAtBestPricesMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | lastQuoteMessage (message : LastQuoteMessage) -- 109
  | benchmarkTradeMessage (message : BenchmarkTradeMessage) -- 58
  | priceLeaderboardMessage (message : PriceLeaderboardMessage) -- 64
  | tradingSniperMessage (message : TradingSniperMessage) -- 60
  | depthAtBestPricesMessage (message : DepthAtBestPricesMessage) -- 94
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .lastQuoteMessage _ => 109
  | .benchmarkTradeMessage _ => 58
  | .priceLeaderboardMessage _ => 64
  | .tradingSniperMessage _ => 60
  | .depthAtBestPricesMessage _ => 94

def encode : Payload → List UInt8
  | .lastQuoteMessage message => LastQuoteMessage.encode message
  | .benchmarkTradeMessage message => BenchmarkTradeMessage.encode message
  | .priceLeaderboardMessage message => PriceLeaderboardMessage.encode message
  | .tradingSniperMessage message => TradingSniperMessage.encode message
  | .depthAtBestPricesMessage message => DepthAtBestPricesMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 73 := by
  cases message with
  | lastQuoteMessage inner =>
    simp only [encode, LastQuoteMessage.encode_length]
    omega
  | benchmarkTradeMessage inner =>
    simp only [encode, BenchmarkTradeMessage.encode_length]
    omega
  | priceLeaderboardMessage inner =>
    simp only [encode, PriceLeaderboardMessage.encode_length]
    omega
  | tradingSniperMessage inner =>
    simp only [encode, TradingSniperMessage.encode_length]
    omega
  | depthAtBestPricesMessage inner =>
    simp only [encode, DepthAtBestPricesMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 109 then (LastQuoteMessage.decode bytes).map fun (message, rest) => (.lastQuoteMessage message, rest)
  else if tag = 58 then (BenchmarkTradeMessage.decode bytes).map fun (message, rest) => (.benchmarkTradeMessage message, rest)
  else if tag = 64 then (PriceLeaderboardMessage.decode bytes).map fun (message, rest) => (.priceLeaderboardMessage message, rest)
  else if tag = 60 then (TradingSniperMessage.decode bytes).map fun (message, rest) => (.tradingSniperMessage message, rest)
  else if tag = 94 then (DepthAtBestPricesMessage.decode bytes).map fun (message, rest) => (.depthAtBestPricesMessage message, rest)
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
  | lastQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LastQuoteMessage.encode_length]
    omega
  | benchmarkTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BenchmarkTradeMessage.encode_length]
    omega
  | priceLeaderboardMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PriceLeaderboardMessage.encode_length]
    omega
  | tradingSniperMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingSniperMessage.encode_length]
    omega
  | depthAtBestPricesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DepthAtBestPricesMessage.encode_length]
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

end Omi.BmvBmvmarketdataProduct29IntraV11
