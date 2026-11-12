import Wire

/-!
# TMX Group Sola Multicast v1.12.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Strike Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Strike Price Fraction
Indicator says (Strike Price Negative Whole Pair, Strike Price Negative Ten Pair, Strike Price
Negative Hundred Pair, Strike Price Negative Thousand Pair, Strike Price Negative Ten Thousand Pair,
Strike Price Negative Hundred Thousand Pair, Strike Price Negative Million Pair, Strike Price
Numeric Pair). It is read as Strike Price Negative Whole Pair's fields, so which arm applies is left
to what is built on the definition.

Note: Trade Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Trade Price Fraction
Indicator says (Trade Price Negative Whole Pair, Trade Price Negative Ten Pair, Trade Price Negative
Hundred Pair, Trade Price Negative Thousand Pair, Trade Price Negative Ten Thousand Pair, Trade
Price Negative Hundred Thousand Pair, Trade Price Negative Million Pair, Trade Price Numeric Pair).
It is read as Trade Price Negative Whole Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Net Change Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Net Change Fraction
Indicator says (Net Change Negative Whole Pair, Net Change Negative Ten Pair, Net Change Negative
Hundred Pair, Net Change Negative Thousand Pair, Net Change Negative Ten Thousand Pair, Net Change
Negative Hundred Thousand Pair, Net Change Negative Million Pair, Net Change Numeric Pair). It is
read as Net Change Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Net Change Future Options Trade Message Fraction Pair is 8 bytes whichever arm the model
names: its arms lay their bytes out alike and differ only in what they are called and what they
mean, which Net Change Fraction Indicator says (Net Change Future Options Trade Message Negative
Whole Pair, Net Change Future Options Trade Message Negative Ten Pair, Net Change Future Options
Trade Message Negative Hundred Pair, Net Change Future Options Trade Message Negative Thousand Pair,
Net Change Future Options Trade Message Negative Ten Thousand Pair, Net Change Future Options Trade
Message Negative Hundred Thousand Pair, Net Change Future Options Trade Message Negative Million
Pair, Net Change Future Options Trade Message Numeric Pair). It is read as Net Change Future Options
Trade Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Strike Price Schedule Notice Fraction Pair is 8 bytes whichever arm the model names: its arms
lay their bytes out alike and differ only in what they are called and what they mean, which Strike
Price Fraction Indicator says (Strike Price Schedule Notice Negative Whole Pair, Strike Price
Schedule Notice Negative Ten Pair, Strike Price Schedule Notice Negative Hundred Pair, Strike Price
Schedule Notice Negative Thousand Pair, Strike Price Schedule Notice Negative Ten Thousand Pair,
Strike Price Schedule Notice Negative Hundred Thousand Pair, Strike Price Schedule Notice Negative
Million Pair, Strike Price Schedule Notice Numeric Pair). It is read as Strike Price Schedule Notice
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Bid Price Quote is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Bid Price Quote Opening says (Bid
Price Quote Opening Pair, Bid Price Quote Numeric Negative Whole Pair, Bid Price Quote Numeric
Negative Ten Pair, Bid Price Quote Numeric Negative Hundred Pair, Bid Price Quote Numeric Negative
Thousand Pair, Bid Price Quote Numeric Negative Ten Thousand Pair, Bid Price Quote Numeric Negative
Hundred Thousand Pair, Bid Price Quote Numeric Negative Million Pair, Bid Price Quote Numeric Pair).
It is read as Bid Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Ask Price Quote is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Ask Price Quote Opening says (Ask
Price Quote Opening Pair, Ask Price Quote Numeric Negative Whole Pair, Ask Price Quote Numeric
Negative Ten Pair, Ask Price Quote Numeric Negative Hundred Pair, Ask Price Quote Numeric Negative
Thousand Pair, Ask Price Quote Numeric Negative Ten Thousand Pair, Ask Price Quote Numeric Negative
Hundred Thousand Pair, Ask Price Quote Numeric Negative Million Pair, Ask Price Quote Numeric Pair).
It is read as Ask Price Quote Numeric Negative Whole Pair's fields, so which arm applies is left to
what is built on the definition.

Note: Number Of Level counts Market Depth Level in ascii digits: it is written from the list as its
digits, and a list of more than 9 could not be written

Note: Ask Price Futures Depth Market Depth Level HF is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which Ask
Price Futures Depth Opening says (Ask Price Futures Depth Market Depth Level HF Opening Pair, Ask
Price Futures Depth Numeric Negative Whole Pair, Ask Price Futures Depth Numeric Negative Ten Pair,
Ask Price Futures Depth Numeric Negative Hundred Pair, Ask Price Futures Depth Numeric Negative
Thousand Pair, Ask Price Futures Depth Numeric Negative Ten Thousand Pair, Ask Price Futures Depth
Numeric Negative Hundred Thousand Pair, Ask Price Futures Depth Numeric Negative Million Pair, Ask
Price Futures Depth Market Depth Level HF Numeric Pair). It is read as Ask Price Futures Depth
Numeric Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Number Of Level counts Futures Market Depth Level in ascii digits: it is written from the list
as its digits, and a list of more than 9 could not be written

Note: Number Of Level counts Strategy Market Depth Level in ascii digits: it is written from the
list as its digits, and a list of more than 9 could not be written

Note: Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Price Fraction Indicator
says (Price Negative Whole Pair, Price Negative Ten Pair, Price Negative Hundred Pair, Price
Negative Thousand Pair, Price Negative Ten Thousand Pair, Price Negative Hundred Thousand Pair,
Price Negative Million Pair, Price Numeric Pair). It is read as Price Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Maximum Threshold Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Maximum
Threshold Price Fraction Indicator says (Maximum Threshold Price Negative Whole Pair, Maximum
Threshold Price Negative Ten Pair, Maximum Threshold Price Negative Hundred Pair, Maximum Threshold
Price Negative Thousand Pair, Maximum Threshold Price Negative Ten Thousand Pair, Maximum Threshold
Price Negative Hundred Thousand Pair, Maximum Threshold Price Negative Million Pair, Maximum
Threshold Price Numeric Pair). It is read as Maximum Threshold Price Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Minimum Threshold Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Minimum
Threshold Price Fraction Indicator says (Minimum Threshold Price Negative Whole Pair, Minimum
Threshold Price Negative Ten Pair, Minimum Threshold Price Negative Hundred Pair, Minimum Threshold
Price Negative Thousand Pair, Minimum Threshold Price Negative Ten Thousand Pair, Minimum Threshold
Price Negative Hundred Thousand Pair, Minimum Threshold Price Negative Million Pair, Minimum
Threshold Price Numeric Pair). It is read as Minimum Threshold Price Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Tick Increment is 8 bytes whichever arm the model names: its arms lay their bytes out alike
and differ only in what they are called and what they mean, which Tick Increment Fraction Indicator
says (Tick Increment Numeric Pair, Tick Increment Numeric Negative Whole Pair, Tick Increment
Numeric Negative Ten Pair, Tick Increment Numeric Negative Hundred Pair, Tick Increment Numeric
Negative Thousand Pair, Tick Increment Numeric Negative Ten Thousand Pair, Tick Increment Numeric
Negative Hundred Thousand Pair, Tick Increment Numeric Negative Million Pair, Tick Increment Raw
Pair). It is read as Tick Increment Numeric Pair's fields, so which arm applies is left to what is
built on the definition.

Note: Tick Value Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Value Fraction
Indicator says (Tick Value Negative Whole Pair, Tick Value Negative Ten Pair, Tick Value Negative
Hundred Pair, Tick Value Negative Thousand Pair, Tick Value Negative Ten Thousand Pair, Tick Value
Negative Hundred Thousand Pair, Tick Value Negative Million Pair, Tick Value Numeric Pair). It is
read as Tick Value Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Maximum Threshold Price Futures Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Maximum Threshold Price Fraction Indicator says (Maximum Threshold Price Futures Negative Whole
Pair, Maximum Threshold Price Futures Negative Ten Pair, Maximum Threshold Price Futures Negative
Hundred Pair, Maximum Threshold Price Futures Negative Thousand Pair, Maximum Threshold Price
Futures Negative Ten Thousand Pair, Maximum Threshold Price Futures Negative Hundred Thousand Pair,
Maximum Threshold Price Futures Negative Million Pair, Maximum Threshold Price Futures Numeric
Pair). It is read as Maximum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Minimum Threshold Price Futures Fraction Pair is 8 bytes whichever arm the model names: its
arms lay their bytes out alike and differ only in what they are called and what they mean, which
Minimum Threshold Price Fraction Indicator says (Minimum Threshold Price Futures Negative Whole
Pair, Minimum Threshold Price Futures Negative Ten Pair, Minimum Threshold Price Futures Negative
Hundred Pair, Minimum Threshold Price Futures Negative Thousand Pair, Minimum Threshold Price
Futures Negative Ten Thousand Pair, Minimum Threshold Price Futures Negative Hundred Thousand Pair,
Minimum Threshold Price Futures Negative Million Pair, Minimum Threshold Price Futures Numeric
Pair). It is read as Minimum Threshold Price Futures Negative Whole Pair's fields, so which arm
applies is left to what is built on the definition.

Note: Number Of Legs counts Strategy Instrument Leg in ascii digits: it is written from the list as
its digits, and a list of more than 99 could not be written

Note: Bid Price Summary Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Bid Price Fraction
Indicator says (Bid Price Summary Negative Whole Pair, Bid Price Summary Negative Ten Pair, Bid
Price Summary Negative Hundred Pair, Bid Price Summary Negative Thousand Pair, Bid Price Summary
Negative Ten Thousand Pair, Bid Price Summary Negative Hundred Thousand Pair, Bid Price Summary
Negative Million Pair, Bid Price Summary Numeric Pair). It is read as Bid Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Ask Price Summary Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Ask Price Fraction
Indicator says (Ask Price Summary Negative Whole Pair, Ask Price Summary Negative Ten Pair, Ask
Price Summary Negative Hundred Pair, Ask Price Summary Negative Thousand Pair, Ask Price Summary
Negative Ten Thousand Pair, Ask Price Summary Negative Hundred Thousand Pair, Ask Price Summary
Negative Million Pair, Ask Price Summary Numeric Pair). It is read as Ask Price Summary Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Last Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Last Price Fraction
Indicator says (Last Price Negative Whole Pair, Last Price Negative Ten Pair, Last Price Negative
Hundred Pair, Last Price Negative Thousand Pair, Last Price Negative Ten Thousand Pair, Last Price
Negative Hundred Thousand Pair, Last Price Negative Million Pair, Last Price Numeric Pair). It is
read as Last Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Open Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Open Price Fraction
Indicator says (Open Price Negative Whole Pair, Open Price Negative Ten Pair, Open Price Negative
Hundred Pair, Open Price Negative Thousand Pair, Open Price Negative Ten Thousand Pair, Open Price
Negative Hundred Thousand Pair, Open Price Negative Million Pair, Open Price Numeric Pair). It is
read as Open Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: High Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which High Price Fraction
Indicator says (High Price Negative Whole Pair, High Price Negative Ten Pair, High Price Negative
Hundred Pair, High Price Negative Thousand Pair, High Price Negative Ten Thousand Pair, High Price
Negative Hundred Thousand Pair, High Price Negative Million Pair, High Price Numeric Pair). It is
read as High Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Low Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Low Price Fraction Indicator
says (Low Price Negative Whole Pair, Low Price Negative Ten Pair, Low Price Negative Hundred Pair,
Low Price Negative Thousand Pair, Low Price Negative Ten Thousand Pair, Low Price Negative Hundred
Thousand Pair, Low Price Negative Million Pair, Low Price Numeric Pair). It is read as Low Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Settlement Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Settlement Price
Fraction Indicator says (Settlement Price Negative Whole Pair, Settlement Price Negative Ten Pair,
Settlement Price Negative Hundred Pair, Settlement Price Negative Thousand Pair, Settlement Price
Negative Ten Thousand Pair, Settlement Price Negative Hundred Thousand Pair, Settlement Price
Negative Million Pair, Settlement Price Numeric Pair). It is read as Settlement Price Negative Whole
Pair's fields, so which arm applies is left to what is built on the definition.

Note: Previous Settlement Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Price Fraction Indicator says (Previous Settlement Price Negative Whole Pair, Previous
Settlement Price Negative Ten Pair, Previous Settlement Price Negative Hundred Pair, Previous
Settlement Price Negative Thousand Pair, Previous Settlement Price Negative Ten Thousand Pair,
Previous Settlement Price Negative Hundred Thousand Pair, Previous Settlement Price Negative Million
Pair, Previous Settlement Price Numeric Pair). It is read as Previous Settlement Price Negative
Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Opening Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Opening Price Fraction
Indicator says (Opening Price Negative Whole Pair, Opening Price Negative Ten Pair, Opening Price
Negative Hundred Pair, Opening Price Negative Thousand Pair, Opening Price Negative Ten Thousand
Pair, Opening Price Negative Hundred Thousand Pair, Opening Price Negative Million Pair, Opening
Price Numeric Pair). It is read as Opening Price Negative Whole Pair's fields, so which arm applies
is left to what is built on the definition.

Note: Settlement Price Future Options Summary Message Fraction Pair is 8 bytes whichever arm the
model names: its arms lay their bytes out alike and differ only in what they are called and what
they mean, which Settlement Price Fraction Indicator says (Settlement Price Future Options Summary
Message Negative Whole Pair, Settlement Price Future Options Summary Message Negative Ten Pair,
Settlement Price Future Options Summary Message Negative Hundred Pair, Settlement Price Future
Options Summary Message Negative Thousand Pair, Settlement Price Future Options Summary Message
Negative Ten Thousand Pair, Settlement Price Future Options Summary Message Negative Hundred
Thousand Pair, Settlement Price Future Options Summary Message Negative Million Pair, Settlement
Price Future Options Summary Message Numeric Pair). It is read as Settlement Price Future Options
Summary Message Negative Whole Pair's fields, so which arm applies is left to what is built on the
definition.

Note: Previous Settlement Fraction Pair is 8 bytes whichever arm the model names: its arms lay their
bytes out alike and differ only in what they are called and what they mean, which Previous
Settlement Fraction Indicator says (Previous Settlement Negative Whole Pair, Previous Settlement
Negative Ten Pair, Previous Settlement Negative Hundred Pair, Previous Settlement Negative Thousand
Pair, Previous Settlement Negative Ten Thousand Pair, Previous Settlement Negative Hundred Thousand
Pair, Previous Settlement Negative Million Pair, Previous Settlement Numeric Pair). It is read as
Previous Settlement Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: External Price At Source Fraction Pair is 8 bytes whichever arm the model names: its arms lay
their bytes out alike and differ only in what they are called and what they mean, which External
Price Fraction Indicator says (External Price At Source Negative Whole Pair, External Price At
Source Negative Ten Pair, External Price At Source Negative Hundred Pair, External Price At Source
Negative Thousand Pair, External Price At Source Negative Ten Thousand Pair, External Price At
Source Negative Hundred Thousand Pair, External Price At Source Negative Million Pair, External
Price At Source Numeric Pair). It is read as External Price At Source Negative Whole Pair's fields,
so which arm applies is left to what is built on the definition.

Note: Min Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes out
alike and differ only in what they are called and what they mean, which Min Price Fraction Indicator
says (Min Price Negative Whole Pair, Min Price Negative Ten Pair, Min Price Negative Hundred Pair,
Min Price Negative Thousand Pair, Min Price Negative Ten Thousand Pair, Min Price Negative Hundred
Thousand Pair, Min Price Negative Million Pair, Min Price Numeric Pair). It is read as Min Price
Negative Whole Pair's fields, so which arm applies is left to what is built on the definition.

Note: Tick Price Fraction Pair is 8 bytes whichever arm the model names: its arms lay their bytes
out alike and differ only in what they are called and what they mean, which Tick Price Fraction
Indicator says (Tick Price Negative Whole Pair, Tick Price Negative Ten Pair, Tick Price Negative
Hundred Pair, Tick Price Negative Thousand Pair, Tick Price Negative Ten Thousand Pair, Tick Price
Negative Hundred Thousand Pair, Tick Price Negative Million Pair, Tick Price Numeric Pair). It is
read as Tick Price Negative Whole Pair's fields, so which arm applies is left to what is built on
the definition.

Note: Nb Entries counts Tick Entry in ascii digits: it is written from the list as its digits, and a
list of more than 99 could not be written

License: MIT No Attribution
-/

namespace Omi.TmxMxSolamulticastHsvfV1122

/-- Exchange Id: one byte code -/
def ExchangeId.codes : List UInt8 :=
  [0x51]

inductive ExchangeId where
  | montreal -- Montreal
  | unlisted (byte : { byte : UInt8 // byte ∉ ExchangeId.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExchangeId

def toByte : ExchangeId → UInt8
  | .montreal => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ExchangeId :=
  .montreal

def ofByte (byte : UInt8) : ExchangeId :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExchangeId) : ofByte value.toByte = value := by
  cases value with
  | montreal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExchangeId) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExchangeId × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExchangeId) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExchangeId) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExchangeId) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExchangeId

/-- Expiry Month: one byte code -/
def ExpiryMonth.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58]

inductive ExpiryMonth where
  | januaryCall -- January Call
  | februaryCall -- February Call
  | marchCall -- March Call
  | aprilCall -- April Call
  | mayCall -- May Call
  | juneCall -- June Call
  | julyCall -- July Call
  | augustCall -- August Call
  | septemberCall -- September Call
  | octoberCall -- October Call
  | novemberCall -- November Call
  | decemberCall -- December Call
  | januaryPut -- January Put
  | februaryPut -- February Put
  | marchPut -- March Put
  | aprilPut -- April Put
  | mayPut -- May Put
  | junePut -- June Put
  | julyPut -- July Put
  | augustPut -- August Put
  | septemberPut -- September Put
  | octoberPut -- October Put
  | novemberPut -- November Put
  | decemberPut -- December Put
  | unlisted (byte : { byte : UInt8 // byte ∉ ExpiryMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExpiryMonth

def toByte : ExpiryMonth → UInt8
  | .januaryCall => 0x41
  | .februaryCall => 0x42
  | .marchCall => 0x43
  | .aprilCall => 0x44
  | .mayCall => 0x45
  | .juneCall => 0x46
  | .julyCall => 0x47
  | .augustCall => 0x48
  | .septemberCall => 0x49
  | .octoberCall => 0x4A
  | .novemberCall => 0x4B
  | .decemberCall => 0x4C
  | .januaryPut => 0x4D
  | .februaryPut => 0x4E
  | .marchPut => 0x4F
  | .aprilPut => 0x50
  | .mayPut => 0x51
  | .junePut => 0x52
  | .julyPut => 0x53
  | .augustPut => 0x54
  | .septemberPut => 0x55
  | .octoberPut => 0x56
  | .novemberPut => 0x57
  | .decemberPut => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExpiryMonth :=
  if byte = 0x41 then .januaryCall
  else if byte = 0x42 then .februaryCall
  else if byte = 0x43 then .marchCall
  else if byte = 0x44 then .aprilCall
  else if byte = 0x45 then .mayCall
  else if byte = 0x46 then .juneCall
  else if byte = 0x47 then .julyCall
  else if byte = 0x48 then .augustCall
  else if byte = 0x49 then .septemberCall
  else if byte = 0x4A then .octoberCall
  else if byte = 0x4B then .novemberCall
  else if byte = 0x4C then .decemberCall
  else if byte = 0x4D then .januaryPut
  else if byte = 0x4E then .februaryPut
  else if byte = 0x4F then .marchPut
  else if byte = 0x50 then .aprilPut
  else if byte = 0x51 then .mayPut
  else if byte = 0x52 then .junePut
  else if byte = 0x53 then .julyPut
  else if byte = 0x54 then .augustPut
  else if byte = 0x55 then .septemberPut
  else if byte = 0x56 then .octoberPut
  else if byte = 0x57 then .novemberPut
  else .decemberPut

def ofByte (byte : UInt8) : ExpiryMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExpiryMonth) : ofByte value.toByte = value := by
  cases value with
  | januaryCall => decide
  | februaryCall => decide
  | marchCall => decide
  | aprilCall => decide
  | mayCall => decide
  | juneCall => decide
  | julyCall => decide
  | augustCall => decide
  | septemberCall => decide
  | octoberCall => decide
  | novemberCall => decide
  | decemberCall => decide
  | januaryPut => decide
  | februaryPut => decide
  | marchPut => decide
  | aprilPut => decide
  | mayPut => decide
  | junePut => decide
  | julyPut => decide
  | augustPut => decide
  | septemberPut => decide
  | octoberPut => decide
  | novemberPut => decide
  | decemberPut => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExpiryMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExpiryMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExpiryMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExpiryMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExpiryMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExpiryMonth

/-- Net Change Sign: one byte code -/
def NetChangeSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive NetChangeSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ NetChangeSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace NetChangeSign

def toByte : NetChangeSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : NetChangeSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : NetChangeSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : NetChangeSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : NetChangeSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (NetChangeSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : NetChangeSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : NetChangeSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : NetChangeSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end NetChangeSign

/-- Price Indicator Marker: one byte code -/
def PriceIndicatorMarker.codes : List UInt8 :=
  [0x41, 0x42, 0x20, 0x44, 0x45, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x52, 0x53, 0x74, 0x54, 0x55, 0x56, 0x59, 0x5A]

inductive PriceIndicatorMarker where
  | asofTrade -- Asof Trade
  | blockTrade -- Block Trade
  | actualTransactionTookPlace -- Actual Transaction Took Place
  | crossed -- Crossed
  | efpReporting -- Efp Reporting
  | contingentTrade -- Contingent Trade
  | risklessBasisCross -- Riskless Basis Cross
  | impliedTrade -- Implied Trade
  | deltaTrade -- Delta Trade
  | committedBlock -- Committed Block
  | lateTrade -- Late Trade
  | forFutureUse -- For Future Use
  | forFutureUse_4e -- For Future Use
  | strategyReporting -- Strategy Reporting
  | forFutureUse_51 -- For Future Use
  | efrReporting -- Efr Reporting
  | referencePrice -- Reference Price
  | tradeCorrection -- Trade Correction
  | committed -- Committed
  | basisOnClose -- Basis On Close
  | priceVolumeAdjustment -- Price Volume Adjustment
  | forFutureUse_59 -- For Future Use
  | forFutureUse_5a -- For Future Use
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceIndicatorMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceIndicatorMarker

def toByte : PriceIndicatorMarker → UInt8
  | .asofTrade => 0x41
  | .blockTrade => 0x42
  | .actualTransactionTookPlace => 0x20
  | .crossed => 0x44
  | .efpReporting => 0x45
  | .contingentTrade => 0x47
  | .risklessBasisCross => 0x48
  | .impliedTrade => 0x49
  | .deltaTrade => 0x4A
  | .committedBlock => 0x4B
  | .lateTrade => 0x4C
  | .forFutureUse => 0x4D
  | .forFutureUse_4e => 0x4E
  | .strategyReporting => 0x50
  | .forFutureUse_51 => 0x51
  | .efrReporting => 0x52
  | .referencePrice => 0x53
  | .tradeCorrection => 0x74
  | .committed => 0x54
  | .basisOnClose => 0x55
  | .priceVolumeAdjustment => 0x56
  | .forFutureUse_59 => 0x59
  | .forFutureUse_5a => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceIndicatorMarker :=
  if byte = 0x41 then .asofTrade
  else if byte = 0x42 then .blockTrade
  else if byte = 0x20 then .actualTransactionTookPlace
  else if byte = 0x44 then .crossed
  else if byte = 0x45 then .efpReporting
  else if byte = 0x47 then .contingentTrade
  else if byte = 0x48 then .risklessBasisCross
  else if byte = 0x49 then .impliedTrade
  else if byte = 0x4A then .deltaTrade
  else if byte = 0x4B then .committedBlock
  else if byte = 0x4C then .lateTrade
  else if byte = 0x4D then .forFutureUse
  else if byte = 0x4E then .forFutureUse_4e
  else if byte = 0x50 then .strategyReporting
  else if byte = 0x51 then .forFutureUse_51
  else if byte = 0x52 then .efrReporting
  else if byte = 0x53 then .referencePrice
  else if byte = 0x74 then .tradeCorrection
  else if byte = 0x54 then .committed
  else if byte = 0x55 then .basisOnClose
  else if byte = 0x56 then .priceVolumeAdjustment
  else if byte = 0x59 then .forFutureUse_59
  else .forFutureUse_5a

def ofByte (byte : UInt8) : PriceIndicatorMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceIndicatorMarker) : ofByte value.toByte = value := by
  cases value with
  | asofTrade => decide
  | blockTrade => decide
  | actualTransactionTookPlace => decide
  | crossed => decide
  | efpReporting => decide
  | contingentTrade => decide
  | risklessBasisCross => decide
  | impliedTrade => decide
  | deltaTrade => decide
  | committedBlock => decide
  | lateTrade => decide
  | forFutureUse => decide
  | forFutureUse_4e => decide
  | strategyReporting => decide
  | forFutureUse_51 => decide
  | efrReporting => decide
  | referencePrice => decide
  | tradeCorrection => decide
  | committed => decide
  | basisOnClose => decide
  | priceVolumeAdjustment => decide
  | forFutureUse_59 => decide
  | forFutureUse_5a => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceIndicatorMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceIndicatorMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceIndicatorMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PriceIndicatorMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PriceIndicatorMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceIndicatorMarker

/-- Symbol Month: one byte code -/
def SymbolMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive SymbolMonth where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolMonth

def toByte : SymbolMonth → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolMonth :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : SymbolMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolMonth) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SymbolMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SymbolMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolMonth

/-- Call Put Code: one byte code -/
def CallPutCode.codes : List UInt8 :=
  [0x43, 0x50]

inductive CallPutCode where
  | call -- Call
  | put -- Put
  | unlisted (byte : { byte : UInt8 // byte ∉ CallPutCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CallPutCode

def toByte : CallPutCode → UInt8
  | .call => 0x43
  | .put => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CallPutCode :=
  if byte = 0x43 then .call
  else .put

def ofByte (byte : UInt8) : CallPutCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CallPutCode) : ofByte value.toByte = value := by
  cases value with
  | call => decide
  | put => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CallPutCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CallPutCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CallPutCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CallPutCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CallPutCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CallPutCode

/-- Trade Price Sign: one byte code -/
def TradePriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive TradePriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ TradePriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradePriceSign

def toByte : TradePriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradePriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : TradePriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradePriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradePriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradePriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradePriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradePriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradePriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradePriceSign

/-- Requested Market Side: one byte code -/
def RequestedMarketSide.codes : List UInt8 :=
  [0x42, 0x53, 0x32]

inductive RequestedMarketSide where
  | buy -- Buy
  | sell -- Sell
  | both -- Both
  | unlisted (byte : { byte : UInt8 // byte ∉ RequestedMarketSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RequestedMarketSide

def toByte : RequestedMarketSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .both => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RequestedMarketSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .both

def ofByte (byte : UInt8) : RequestedMarketSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RequestedMarketSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | both => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RequestedMarketSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RequestedMarketSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RequestedMarketSide) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RequestedMarketSide) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RequestedMarketSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RequestedMarketSide

/-- Series Status: one byte code -/
def SeriesStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive SeriesStatus where
  | preOpening -- Pre Opening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endOfDayInquiries -- End Of Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ SeriesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SeriesStatus

def toByte : SeriesStatus → UInt8
  | .preOpening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endOfDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SeriesStatus :=
  if byte = 0x59 then .preOpening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endOfDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : SeriesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SeriesStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endOfDayInquiries => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SeriesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SeriesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SeriesStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SeriesStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SeriesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SeriesStatus

/-- Instrument Status Marker: one byte code -/
def InstrumentStatusMarker.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x52, 0x53, 0x41, 0x43, 0x20]

inductive InstrumentStatusMarker where
  | preopening -- Preopening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | reserved -- Reserved
  | suspended -- Suspended
  | surveillanceIntervention -- Surveillance Intervention
  | endofDayInquiries -- Endof Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatusMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatusMarker

def toByte : InstrumentStatusMarker → UInt8
  | .preopening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .reserved => 0x52
  | .suspended => 0x53
  | .surveillanceIntervention => 0x41
  | .endofDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatusMarker :=
  if byte = 0x59 then .preopening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x52 then .reserved
  else if byte = 0x53 then .suspended
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endofDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : InstrumentStatusMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatusMarker) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | reserved => decide
  | suspended => decide
  | surveillanceIntervention => decide
  | endofDayInquiries => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatusMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatusMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatusMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentStatusMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentStatusMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatusMarker

/-- Bid Price Sign: one byte code -/
def BidPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive BidPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ BidPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BidPriceSign

def toByte : BidPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BidPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : BidPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BidPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BidPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BidPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BidPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BidPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BidPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BidPriceSign

/-- Ask Price Sign: one byte code -/
def AskPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive AskPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ AskPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AskPriceSign

def toByte : AskPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AskPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : AskPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AskPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AskPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AskPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AskPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AskPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AskPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AskPriceSign

/-- Level Of Market Depth: one byte code -/
def LevelOfMarketDepth.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x41]

inductive LevelOfMarketDepth where
  | level1 -- Level 1
  | level2 -- Level 2
  | level3 -- Level 3
  | level4 -- Level 4
  | level5 -- Level 5
  | implied -- Implied
  | unlisted (byte : { byte : UInt8 // byte ∉ LevelOfMarketDepth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LevelOfMarketDepth

def toByte : LevelOfMarketDepth → UInt8
  | .level1 => 0x31
  | .level2 => 0x32
  | .level3 => 0x33
  | .level4 => 0x34
  | .level5 => 0x35
  | .implied => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LevelOfMarketDepth :=
  if byte = 0x31 then .level1
  else if byte = 0x32 then .level2
  else if byte = 0x33 then .level3
  else if byte = 0x34 then .level4
  else if byte = 0x35 then .level5
  else .implied

def ofByte (byte : UInt8) : LevelOfMarketDepth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LevelOfMarketDepth) : ofByte value.toByte = value := by
  cases value with
  | level1 => decide
  | level2 => decide
  | level3 => decide
  | level4 => decide
  | level5 => decide
  | implied => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LevelOfMarketDepth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LevelOfMarketDepth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LevelOfMarketDepth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LevelOfMarketDepth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LevelOfMarketDepth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LevelOfMarketDepth

/-- Option Type: one byte code -/
def OptionType.codes : List UInt8 :=
  [0x41, 0x45]

inductive OptionType where
  | american -- American
  | european -- European
  | unlisted (byte : { byte : UInt8 // byte ∉ OptionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OptionType

def toByte : OptionType → UInt8
  | .american => 0x41
  | .european => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OptionType :=
  if byte = 0x41 then .american
  else .european

def ofByte (byte : UInt8) : OptionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OptionType) : ofByte value.toByte = value := by
  cases value with
  | american => decide
  | european => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OptionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OptionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OptionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OptionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OptionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OptionType

/-- Delivery Type: one byte code -/
def DeliveryType.codes : List UInt8 :=
  [0x43, 0x50]

inductive DeliveryType where
  | cash -- Cash
  | physical -- Physical
  | unlisted (byte : { byte : UInt8 // byte ∉ DeliveryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeliveryType

def toByte : DeliveryType → UInt8
  | .cash => 0x43
  | .physical => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeliveryType :=
  if byte = 0x43 then .cash
  else .physical

def ofByte (byte : UInt8) : DeliveryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeliveryType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | physical => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeliveryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeliveryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeliveryType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : DeliveryType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : DeliveryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeliveryType

/-- Underlying Symbol Month: one byte code -/
def UnderlyingSymbolMonth.codes : List UInt8 :=
  [0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x51, 0x55, 0x56, 0x58, 0x5A]

inductive UnderlyingSymbolMonth where
  | january -- January
  | february -- February
  | march -- March
  | april -- April
  | may -- May
  | june -- June
  | july -- July
  | august -- August
  | september -- September
  | october -- October
  | november -- November
  | december -- December
  | unlisted (byte : { byte : UInt8 // byte ∉ UnderlyingSymbolMonth.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UnderlyingSymbolMonth

def toByte : UnderlyingSymbolMonth → UInt8
  | .january => 0x46
  | .february => 0x47
  | .march => 0x48
  | .april => 0x4A
  | .may => 0x4B
  | .june => 0x4D
  | .july => 0x4E
  | .august => 0x51
  | .september => 0x55
  | .october => 0x56
  | .november => 0x58
  | .december => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : UnderlyingSymbolMonth :=
  if byte = 0x46 then .january
  else if byte = 0x47 then .february
  else if byte = 0x48 then .march
  else if byte = 0x4A then .april
  else if byte = 0x4B then .may
  else if byte = 0x4D then .june
  else if byte = 0x4E then .july
  else if byte = 0x51 then .august
  else if byte = 0x55 then .september
  else if byte = 0x56 then .october
  else if byte = 0x58 then .november
  else .december

def ofByte (byte : UInt8) : UnderlyingSymbolMonth :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UnderlyingSymbolMonth) : ofByte value.toByte = value := by
  cases value with
  | january => decide
  | february => decide
  | march => decide
  | april => decide
  | may => decide
  | june => decide
  | july => decide
  | august => decide
  | september => decide
  | october => decide
  | november => decide
  | december => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UnderlyingSymbolMonth) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UnderlyingSymbolMonth × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UnderlyingSymbolMonth) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UnderlyingSymbolMonth) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UnderlyingSymbolMonth) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UnderlyingSymbolMonth

/-- Strategy Allow Implied: one byte code -/
def StrategyAllowImplied.codes : List UInt8 :=
  [0x59, 0x4E]

inductive StrategyAllowImplied where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyAllowImplied.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyAllowImplied

def toByte : StrategyAllowImplied → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyAllowImplied :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : StrategyAllowImplied :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyAllowImplied) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyAllowImplied) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyAllowImplied × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyAllowImplied) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyAllowImplied) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyAllowImplied) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyAllowImplied

/-- Leg Ratio Sign: one byte code -/
def LegRatioSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LegRatioSign where
  | buyOfTheUnderlying -- Buy Of The Underlying
  | sellOfTheUnderlying -- Sell Of The Underlying
  | unlisted (byte : { byte : UInt8 // byte ∉ LegRatioSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegRatioSign

def toByte : LegRatioSign → UInt8
  | .buyOfTheUnderlying => 0x2B
  | .sellOfTheUnderlying => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegRatioSign :=
  if byte = 0x2B then .buyOfTheUnderlying
  else .sellOfTheUnderlying

def ofByte (byte : UInt8) : LegRatioSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegRatioSign) : ofByte value.toByte = value := by
  cases value with
  | buyOfTheUnderlying => decide
  | sellOfTheUnderlying => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegRatioSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegRatioSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegRatioSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegRatioSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegRatioSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegRatioSign

/-- Tick: one byte code -/
def Tick.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive Tick where
  | uptick -- Uptick
  | downtick -- Downtick
  | unlisted (byte : { byte : UInt8 // byte ∉ Tick.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tick

def toByte : Tick → UInt8
  | .uptick => 0x2B
  | .downtick => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tick :=
  if byte = 0x2B then .uptick
  else .downtick

def ofByte (byte : UInt8) : Tick :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tick) : ofByte value.toByte = value := by
  cases value with
  | uptick => decide
  | downtick => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tick) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tick × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tick) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Tick) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Tick) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tick

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x53, 0x45, 0x55, 0x43]

inductive Reason where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | instrumentNewOrUpdate -- Instrument New Or Update
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .instrumentNewOrUpdate => 0x55
  | .tradeCancellation => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x53 then .startOfDay
  else if byte = 0x45 then .endOfDay
  else if byte = 0x55 then .instrumentNewOrUpdate
  else .tradeCancellation

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | instrumentNewOrUpdate => decide
  | tradeCancellation => decide
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

/-- Last Price Sign: one byte code -/
def LastPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LastPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LastPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastPriceSign

def toByte : LastPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LastPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastPriceSign

/-- Open Price Sign: one byte code -/
def OpenPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive OpenPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenPriceSign

def toByte : OpenPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : OpenPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OpenPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OpenPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenPriceSign

/-- High Price Sign: one byte code -/
def HighPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive HighPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ HighPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HighPriceSign

def toByte : HighPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HighPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : HighPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HighPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HighPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : HighPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : HighPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HighPriceSign

/-- Low Price Sign: one byte code -/
def LowPriceSign.codes : List UInt8 :=
  [0x2B, 0x2D]

inductive LowPriceSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ LowPriceSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LowPriceSign

def toByte : LowPriceSign → UInt8
  | .positive => 0x2B
  | .negative => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LowPriceSign :=
  if byte = 0x2B then .positive
  else .negative

def ofByte (byte : UInt8) : LowPriceSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LowPriceSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LowPriceSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPriceSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPriceSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LowPriceSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LowPriceSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LowPriceSign

/-- Group Status: one byte code -/
def GroupStatus.codes : List UInt8 :=
  [0x59, 0x4F, 0x54, 0x46, 0x45, 0x48, 0x41, 0x43, 0x20]

inductive GroupStatus where
  | preOpening -- Pre Opening
  | opening -- Opening
  | continuousTrading -- Continuous Trading
  | forbidden -- Forbidden
  | interventionBeforeOpening -- Intervention Before Opening
  | haltedTrading -- Halted Trading
  | surveillanceIntervention -- Surveillance Intervention
  | endOfDayInquiries -- End Of Day Inquiries
  | ifNotUsed -- If Not Used
  | unlisted (byte : { byte : UInt8 // byte ∉ GroupStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GroupStatus

def toByte : GroupStatus → UInt8
  | .preOpening => 0x59
  | .opening => 0x4F
  | .continuousTrading => 0x54
  | .forbidden => 0x46
  | .interventionBeforeOpening => 0x45
  | .haltedTrading => 0x48
  | .surveillanceIntervention => 0x41
  | .endOfDayInquiries => 0x43
  | .ifNotUsed => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GroupStatus :=
  if byte = 0x59 then .preOpening
  else if byte = 0x4F then .opening
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x46 then .forbidden
  else if byte = 0x45 then .interventionBeforeOpening
  else if byte = 0x48 then .haltedTrading
  else if byte = 0x41 then .surveillanceIntervention
  else if byte = 0x43 then .endOfDayInquiries
  else .ifNotUsed

def ofByte (byte : UInt8) : GroupStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GroupStatus) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | opening => decide
  | continuousTrading => decide
  | forbidden => decide
  | interventionBeforeOpening => decide
  | haltedTrading => decide
  | surveillanceIntervention => decide
  | endOfDayInquiries => decide
  | ifNotUsed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GroupStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GroupStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GroupStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : GroupStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : GroupStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GroupStatus

/-- Continue Marker: one byte code -/
def ContinueMarker.codes : List UInt8 :=
  [0x30, 0x31]

inductive ContinueMarker where
  | bulletinContinuesInNextRecord -- Bulletin Continues In Next Record
  | bulletinEnded -- Bulletin Ended
  | unlisted (byte : { byte : UInt8 // byte ∉ ContinueMarker.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContinueMarker

def toByte : ContinueMarker → UInt8
  | .bulletinContinuesInNextRecord => 0x30
  | .bulletinEnded => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContinueMarker :=
  if byte = 0x30 then .bulletinContinuesInNextRecord
  else .bulletinEnded

def ofByte (byte : UInt8) : ContinueMarker :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContinueMarker) : ofByte value.toByte = value := by
  cases value with
  | bulletinContinuesInNextRecord => decide
  | bulletinEnded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContinueMarker) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContinueMarker × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContinueMarker) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ContinueMarker) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ContinueMarker) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContinueMarker

/-- Long Message Header: 12 bytes -/
structure LongMessageHeader where
  messageTimestamp : Alpha 12
  deriving DecidableEq, Repr

namespace LongMessageHeader

def encode (message : LongMessageHeader) : List UInt8 :=
  Alpha.encode message.messageTimestamp

def decode (bytes : List UInt8) : Option (LongMessageHeader × List UInt8) := do
  let (messageTimestamp, bytes) ← Alpha.decode 12 bytes
  pure ({ messageTimestamp }, bytes)

@[simp] theorem encode_length (message : LongMessageHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LongMessageHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongMessageHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongMessageHeader

/-- Strike Price Fraction Pair: 8 bytes -/
structure StrikePriceFractionPair where
  rawStrikePrice : Alpha 7
  strikePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceFractionPair

def encode (message : StrikePriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawStrikePrice
    ++ (encodeUInt 1 message.strikePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (StrikePriceFractionPair × List UInt8) := do
  let (rawStrikePrice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawStrikePrice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrikePriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StrikePriceFractionPair

/-- Option Symbol: 20 bytes -/
structure OptionSymbol where
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceFractionPair : StrikePriceFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbol

def encode (message : OptionSymbol) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceFractionPair.encode message.strikePriceFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay)))))

def decode (bytes : List UInt8) : Option (OptionSymbol × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceFractionPair, bytes) ← StrikePriceFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, expiryMonth, filler1, strikePriceFractionPair, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceFractionPair.encode_length]

theorem encode_length_pos (message : OptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbol

/-- Trade Price Fraction Pair: 8 bytes -/
structure TradePriceFractionPair where
  rawTradePrice : Alpha 7
  tradePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TradePriceFractionPair

def encode (message : TradePriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTradePrice
    ++ (encodeUInt 1 message.tradePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TradePriceFractionPair × List UInt8) := do
  let (rawTradePrice, bytes) ← Alpha.decode 7 bytes
  let (tradePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTradePrice, tradePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TradePriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TradePriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradePriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradePriceFractionPair

/-- Net Change Fraction Pair: 8 bytes -/
structure NetChangeFractionPair where
  rawNetChange : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFractionPair

def encode (message : NetChangeFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChange
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFractionPair × List UInt8) := do
  let (rawNetChange, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChange, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFractionPair

/-- Option Trade Message: 83 bytes -/
structure OptionTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeMessage

def encode (message : OptionTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))

def decode (bytes : List UInt8) : Option (OptionTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, tradeTimestamp, filler1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeMessage

/-- Future Option Symbol: 20 bytes -/
structure FutureOptionSymbol where
  rootSymbol : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  callPutCode : CallPutCode
  strikePriceFractionPair : StrikePriceFractionPair
  deriving DecidableEq, Repr

namespace FutureOptionSymbol

def encode (message : FutureOptionSymbol) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay
    ++ (CallPutCode.encode message.callPutCode
    ++ (StrikePriceFractionPair.encode message.strikePriceFractionPair)))))

def decode (bytes : List UInt8) : Option (FutureOptionSymbol × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (callPutCode, bytes) ← CallPutCode.decode bytes
  let (strikePriceFractionPair, bytes) ← StrikePriceFractionPair.decode bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay, callPutCode, strikePriceFractionPair }, bytes)

@[simp] theorem encode_length (message : FutureOptionSymbol) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length, CallPutCode.encode_length, StrikePriceFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionSymbol) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionSymbol) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CallPutCode.decode_encode, some_bind]
  dsimp only
  rw [StrikePriceFractionPair.decode_encode, some_bind]
  rfl

end FutureOptionSymbol

/-- Net Change Future Options Trade Message Fraction Pair: 8 bytes -/
structure NetChangeFutureOptionsTradeMessageFractionPair where
  rawNetChangeFutureOptionsTradeMessage : Alpha 7
  netChangeFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace NetChangeFutureOptionsTradeMessageFractionPair

def encode (message : NetChangeFutureOptionsTradeMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawNetChangeFutureOptionsTradeMessage
    ++ (encodeUInt 1 message.netChangeFractionIndicator)

def decode (bytes : List UInt8) : Option (NetChangeFutureOptionsTradeMessageFractionPair × List UInt8) := do
  let (rawNetChangeFutureOptionsTradeMessage, bytes) ← Alpha.decode 7 bytes
  let (netChangeFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawNetChangeFutureOptionsTradeMessage, netChangeFractionIndicator }, bytes)

@[simp] theorem encode_length (message : NetChangeFutureOptionsTradeMessageFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NetChangeFutureOptionsTradeMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NetChangeFutureOptionsTradeMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NetChangeFutureOptionsTradeMessageFractionPair

/-- Future Options Trade Message: 84 bytes -/
structure FutureOptionsTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  netChangeSign : NetChangeSign
  netChangeFutureOptionsTradeMessageFractionPair : NetChangeFutureOptionsTradeMessageFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeMessage

def encode (message : FutureOptionsTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFutureOptionsTradeMessageFractionPair.encode message.netChangeFutureOptionsTradeMessageFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber)))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFutureOptionsTradeMessageFractionPair, bytes) ← NetChangeFutureOptionsTradeMessageFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, volume, tradePriceFractionPair, priceIndicatorMarker, netChangeSign, netChangeFutureOptionsTradeMessageFractionPair, filler6, tradeTimestamp, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length, NetChangeSign.encode_length, NetChangeFutureOptionsTradeMessageFractionPair.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFutureOptionsTradeMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeMessage

/-- Future Product: 11 bytes -/
structure FutureProduct where
  rootSymbol : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace FutureProduct

def encode (message : FutureProduct) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (FutureProduct × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : FutureProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length]

theorem encode_length_pos (message : FutureProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureProduct

/-- Futures Trade Message: 73 bytes -/
structure FuturesTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeMessage

def encode (message : FuturesTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeMessage

/-- Strategy Trade Message: 93 bytes -/
structure StrategyTradeMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeMessage

def encode (message : StrategyTradeMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeMessage) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, TradePriceSign.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : StrategyTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeMessage

/-- Option Request For Quote Rfq Message: 42 bytes -/
structure OptionRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace OptionRequestForQuoteRfqMessage

def encode (message : OptionRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (OptionRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : OptionRequestForQuoteRfqMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : OptionRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end OptionRequestForQuoteRfqMessage

/-- Future Options Request For Quote Rfq Message: 42 bytes -/
structure FutureOptionsRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FutureOptionsRequestForQuoteRfqMessage

def encode (message : FutureOptionsRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (FutureOptionsRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FutureOptionsRequestForQuoteRfqMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FutureOptionsRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FutureOptionsRequestForQuoteRfqMessage

/-- Futures Request For Quote Rfq Message: 33 bytes -/
structure FuturesRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace FuturesRequestForQuoteRfqMessage

def encode (message : FuturesRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (FuturesRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : FuturesRequestForQuoteRfqMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : FuturesRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end FuturesRequestForQuoteRfqMessage

/-- Strategy Request For Quote Rfq Message: 52 bytes -/
structure StrategyRequestForQuoteRfqMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  symbol : Alpha 30
  requestedSize : Alpha 8
  requestedMarketSide : RequestedMarketSide
  deriving DecidableEq, Repr

namespace StrategyRequestForQuoteRfqMessage

def encode (message : StrategyRequestForQuoteRfqMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.requestedSize
    ++ (RequestedMarketSide.encode message.requestedMarketSide))))

def decode (bytes : List UInt8) : Option (StrategyRequestForQuoteRfqMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (requestedSize, bytes) ← Alpha.decode 8 bytes
  let (requestedMarketSide, bytes) ← RequestedMarketSide.decode bytes
  pure ({ longMessageHeader, exchangeId, symbol, requestedSize, requestedMarketSide }, bytes)

@[simp] theorem encode_length (message : StrategyRequestForQuoteRfqMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, RequestedMarketSide.encode_length]

theorem encode_length_pos (message : StrategyRequestForQuoteRfqMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyRequestForQuoteRfqMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestedMarketSide.decode_encode, some_bind]
  rfl

end StrategyRequestForQuoteRfqMessage

/-- Strike Price Schedule Notice Fraction Pair: 8 bytes -/
structure StrikePriceScheduleNoticeFractionPair where
  rawStrikePriceScheduleNotice : Alpha 7
  strikePriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePriceScheduleNoticeFractionPair

def encode (message : StrikePriceScheduleNoticeFractionPair) : List UInt8 :=
  Alpha.encode message.rawStrikePriceScheduleNotice
    ++ (encodeUInt 1 message.strikePriceFractionIndicator)

def decode (bytes : List UInt8) : Option (StrikePriceScheduleNoticeFractionPair × List UInt8) := do
  let (rawStrikePriceScheduleNotice, bytes) ← Alpha.decode 7 bytes
  let (strikePriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawStrikePriceScheduleNotice, strikePriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : StrikePriceScheduleNoticeFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePriceScheduleNoticeFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePriceScheduleNoticeFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StrikePriceScheduleNoticeFractionPair

/-- Option Symbol Schedule Notice: 20 bytes -/
structure OptionSymbolScheduleNotice where
  rootSymbol : Alpha 6
  expiryMonth : ExpiryMonth
  filler1 : Alpha 1
  strikePriceScheduleNoticeFractionPair : StrikePriceScheduleNoticeFractionPair
  expiryYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace OptionSymbolScheduleNotice

def encode (message : OptionSymbolScheduleNotice) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (ExpiryMonth.encode message.expiryMonth
    ++ (Alpha.encode message.filler1
    ++ (StrikePriceScheduleNoticeFractionPair.encode message.strikePriceScheduleNoticeFractionPair
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryDay)))))

def decode (bytes : List UInt8) : Option (OptionSymbolScheduleNotice × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (expiryMonth, bytes) ← ExpiryMonth.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (strikePriceScheduleNoticeFractionPair, bytes) ← StrikePriceScheduleNoticeFractionPair.decode bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, expiryMonth, filler1, strikePriceScheduleNoticeFractionPair, expiryYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : OptionSymbolScheduleNotice) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ExpiryMonth.encode_length, StrikePriceScheduleNoticeFractionPair.encode_length]

theorem encode_length_pos (message : OptionSymbolScheduleNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSymbolScheduleNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExpiryMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrikePriceScheduleNoticeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionSymbolScheduleNotice

/-- Instrument Schedule Notice Option Message: 40 bytes -/
structure InstrumentScheduleNoticeOptionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbolScheduleNotice : OptionSymbolScheduleNotice
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeOptionMessage

def encode (message : InstrumentScheduleNoticeOptionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbolScheduleNotice.encode message.optionSymbolScheduleNotice
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeOptionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbolScheduleNotice, bytes) ← OptionSymbolScheduleNotice.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbolScheduleNotice, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbolScheduleNotice.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbolScheduleNotice.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeOptionMessage

/-- Instrument Schedule Notice Futures Option Message: 40 bytes -/
structure InstrumentScheduleNoticeFuturesOptionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFuturesOptionMessage

def encode (message : InstrumentScheduleNoticeFuturesOptionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFuturesOptionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFuturesOptionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFuturesOptionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFuturesOptionMessage

/-- Instrument Schedule Notice Future Message: 31 bytes -/
structure InstrumentScheduleNoticeFutureMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeFutureMessage

def encode (message : InstrumentScheduleNoticeFutureMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeFutureMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, SeriesStatus.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeFutureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeFutureMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeFutureMessage

/-- Instrument Schedule Notice Strategy Message: 50 bytes -/
structure InstrumentScheduleNoticeStrategyMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  seriesStatus : SeriesStatus
  scheduledStatusChangeTime : Alpha 6
  deriving DecidableEq, Repr

namespace InstrumentScheduleNoticeStrategyMessage

def encode (message : InstrumentScheduleNoticeStrategyMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (SeriesStatus.encode message.seriesStatus
    ++ (Alpha.encode message.scheduledStatusChangeTime))))

def decode (bytes : List UInt8) : Option (InstrumentScheduleNoticeStrategyMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (seriesStatus, bytes) ← SeriesStatus.decode bytes
  let (scheduledStatusChangeTime, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, strategySymbol, seriesStatus, scheduledStatusChangeTime }, bytes)

@[simp] theorem encode_length (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, SeriesStatus.encode_length]

theorem encode_length_pos (message : InstrumentScheduleNoticeStrategyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentScheduleNoticeStrategyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SeriesStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentScheduleNoticeStrategyMessage

/-- Bid Price Quote: 8 bytes -/
structure BidPriceQuote where
  rawBidPriceQuoteNumeric : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceQuote

def encode (message : BidPriceQuote) : List UInt8 :=
  Alpha.encode message.rawBidPriceQuoteNumeric
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceQuote × List UInt8) := do
  let (rawBidPriceQuoteNumeric, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceQuoteNumeric, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceQuote) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceQuote

/-- Ask Price Quote: 8 bytes -/
structure AskPriceQuote where
  rawAskPriceQuoteNumeric : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceQuote

def encode (message : AskPriceQuote) : List UInt8 :=
  Alpha.encode message.rawAskPriceQuoteNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceQuote × List UInt8) := do
  let (rawAskPriceQuoteNumeric, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceQuoteNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceQuote) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceQuote) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceQuote) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceQuote

/-- Option Quote Message: 61 bytes -/
structure OptionQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  filler1 : Alpha 1
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace OptionQuoteMessage

def encode (message : OptionQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.filler1
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker))))))))

def decode (bytes : List UInt8) : Option (OptionQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, bidPriceQuote, bidSize, askPriceQuote, askSize, filler1, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : OptionQuoteMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : OptionQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end OptionQuoteMessage

/-- Future Options Quote Message: 61 bytes -/
structure FutureOptionsQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  filler1 : Alpha 1
  deriving DecidableEq, Repr

namespace FutureOptionsQuoteMessage

def encode (message : FutureOptionsQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (Alpha.encode message.filler1))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, bidPriceQuote, bidSize, askPriceQuote, askSize, instrumentStatusMarker, filler1 }, bytes)

@[simp] theorem encode_length (message : FutureOptionsQuoteMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsQuoteMessage

/-- Futures Quote Message: 51 bytes -/
structure FuturesQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace FuturesQuoteMessage

def encode (message : FuturesQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker)))))))

def decode (bytes : List UInt8) : Option (FuturesQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, bidPriceQuote, bidSize, askPriceQuote, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : FuturesQuoteMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : FuturesQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end FuturesQuoteMessage

/-- Strategy Quote Message: 72 bytes -/
structure StrategyQuoteMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  symbol : Alpha 30
  bidPriceSign : BidPriceSign
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  instrumentStatusMarker : InstrumentStatusMarker
  deriving DecidableEq, Repr

namespace StrategyQuoteMessage

def encode (message : StrategyQuoteMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker)))))))))

def decode (bytes : List UInt8) : Option (StrategyQuoteMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  pure ({ longMessageHeader, exchangeId, symbol, bidPriceSign, bidPriceQuote, bidSize, askPriceSign, askPriceQuote, askSize, instrumentStatusMarker }, bytes)

@[simp] theorem encode_length (message : StrategyQuoteMessage) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceQuote.encode_length, AskPriceSign.encode_length, AskPriceQuote.encode_length, InstrumentStatusMarker.encode_length]

theorem encode_length_pos (message : StrategyQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [InstrumentStatusMarker.decode_encode, some_bind]
  rfl

end StrategyQuoteMessage

/-- Market Depth Level: 31 bytes -/
structure MarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace MarketDepthLevel

def encode (message : MarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (MarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidSize, numberOfBidOrders, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : MarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : MarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MarketDepthLevel

/-- Option Market Depth Message -/
structure OptionMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace OptionMarketDepthMessage

def encode (message : OptionMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (OptionMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevel bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, optionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : OptionMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OptionMarketDepthMessage) : (encode message).length ≤ 314 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : OptionMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end OptionMarketDepthMessage

/-- Future Options Market Depth Message -/
structure FutureOptionsMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  instrumentStatusMarker : InstrumentStatusMarker
  marketDepthLevel : Digited 1 MarketDepthLevel
  deriving DecidableEq, Repr

namespace FutureOptionsMarketDepthMessage

def encode (message : FutureOptionsMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.marketDepthLevel.val.length
    ++ (encodeMany MarketDepthLevel.encode message.marketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (FutureOptionsMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (marketDepthLevel_, bytes) ← decodeMany MarketDepthLevel.decode numberOfLevel bytes
  if fits_marketDepthLevel : marketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, futureOptionSymbol, instrumentStatusMarker, marketDepthLevel := ⟨marketDepthLevel_, fits_marketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FutureOptionsMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FutureOptionsMarketDepthMessage) : (encode message).length ≤ 314 := by
  have bound_marketDepthLevel := message.marketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const MarketDepthLevel.encode 31 MarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FutureOptionsMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.marketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany MarketDepthLevel.encode MarketDepthLevel.decode MarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDepthLevel.length_lt]
  rfl

end FutureOptionsMarketDepthMessage

/-- Ask Price Futures Depth Market Depth Level HF: 8 bytes -/
structure AskPriceFuturesDepthMarketDepthLevelHf where
  rawAskPriceFuturesDepthNumeric : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceFuturesDepthMarketDepthLevelHf

def encode (message : AskPriceFuturesDepthMarketDepthLevelHf) : List UInt8 :=
  Alpha.encode message.rawAskPriceFuturesDepthNumeric
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceFuturesDepthMarketDepthLevelHf × List UInt8) := do
  let (rawAskPriceFuturesDepthNumeric, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceFuturesDepthNumeric, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceFuturesDepthMarketDepthLevelHf) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceFuturesDepthMarketDepthLevelHf) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceFuturesDepthMarketDepthLevelHf) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceFuturesDepthMarketDepthLevelHf

/-- Futures Market Depth Level: 31 bytes -/
structure FuturesMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceFuturesDepthMarketDepthLevelHf : AskPriceFuturesDepthMarketDepthLevelHf
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace FuturesMarketDepthLevel

def encode (message : FuturesMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceFuturesDepthMarketDepthLevelHf.encode message.askPriceFuturesDepthMarketDepthLevelHf
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceFuturesDepthMarketDepthLevelHf, bytes) ← AskPriceFuturesDepthMarketDepthLevelHf.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceQuote, bidSize, numberOfBidOrders, askPriceFuturesDepthMarketDepthLevelHf, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : FuturesMarketDepthLevel) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceFuturesDepthMarketDepthLevelHf.encode_length]

theorem encode_length_pos (message : FuturesMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceFuturesDepthMarketDepthLevelHf.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesMarketDepthLevel

/-- Futures Market Depth Message -/
structure FuturesMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  instrumentStatusMarker : InstrumentStatusMarker
  futuresMarketDepthLevel : Digited 1 FuturesMarketDepthLevel
  deriving DecidableEq, Repr

namespace FuturesMarketDepthMessage

def encode (message : FuturesMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.futuresMarketDepthLevel.val.length
    ++ (encodeMany FuturesMarketDepthLevel.encode message.futuresMarketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (FuturesMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (futuresMarketDepthLevel_, bytes) ← decodeMany FuturesMarketDepthLevel.decode numberOfLevel bytes
  if fits_futuresMarketDepthLevel : futuresMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, futureProduct, instrumentStatusMarker, futuresMarketDepthLevel := ⟨futuresMarketDepthLevel_, fits_futuresMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : FuturesMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FuturesMarketDepthMessage) : (encode message).length ≤ 305 := by
  have bound_futuresMarketDepthLevel := message.futuresMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const FuturesMarketDepthLevel.encode 31 FuturesMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : FuturesMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.futuresMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany FuturesMarketDepthLevel.encode FuturesMarketDepthLevel.decode FuturesMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.futuresMarketDepthLevel.length_lt]
  rfl

end FuturesMarketDepthMessage

/-- Strategy Market Depth Level: 33 bytes -/
structure StrategyMarketDepthLevel where
  levelOfMarketDepth : LevelOfMarketDepth
  bidPriceSign : BidPriceSign
  bidPriceQuote : BidPriceQuote
  bidSize : Alpha 5
  numberOfBidOrders : Alpha 2
  askPriceSign : AskPriceSign
  askPriceQuote : AskPriceQuote
  askSize : Alpha 5
  numberOfAskOrders : Alpha 2
  deriving DecidableEq, Repr

namespace StrategyMarketDepthLevel

def encode (message : StrategyMarketDepthLevel) : List UInt8 :=
  LevelOfMarketDepth.encode message.levelOfMarketDepth
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceQuote.encode message.bidPriceQuote
    ++ (Alpha.encode message.bidSize
    ++ (Alpha.encode message.numberOfBidOrders
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceQuote.encode message.askPriceQuote
    ++ (Alpha.encode message.askSize
    ++ (Alpha.encode message.numberOfAskOrders))))))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthLevel × List UInt8) := do
  let (levelOfMarketDepth, bytes) ← LevelOfMarketDepth.decode bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceQuote, bytes) ← BidPriceQuote.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfBidOrders, bytes) ← Alpha.decode 2 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceQuote, bytes) ← AskPriceQuote.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (numberOfAskOrders, bytes) ← Alpha.decode 2 bytes
  pure ({ levelOfMarketDepth, bidPriceSign, bidPriceQuote, bidSize, numberOfBidOrders, askPriceSign, askPriceQuote, askSize, numberOfAskOrders }, bytes)

@[simp] theorem encode_length (message : StrategyMarketDepthLevel) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, LevelOfMarketDepth.encode_length, BidPriceSign.encode_length, BidPriceQuote.encode_length, Alpha.encode_length, AskPriceSign.encode_length, AskPriceQuote.encode_length]

theorem encode_length_pos (message : StrategyMarketDepthLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyMarketDepthLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LevelOfMarketDepth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceQuote.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyMarketDepthLevel

/-- Strategy Market Depth Message -/
structure StrategyMarketDepthMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  symbol : Alpha 30
  instrumentStatusMarker : InstrumentStatusMarker
  strategyMarketDepthLevel : Digited 1 StrategyMarketDepthLevel
  deriving DecidableEq, Repr

namespace StrategyMarketDepthMessage

def encode (message : StrategyMarketDepthMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (InstrumentStatusMarker.encode message.instrumentStatusMarker
    ++ (encodeDigits 1 message.strategyMarketDepthLevel.val.length
    ++ (encodeMany StrategyMarketDepthLevel.encode message.strategyMarketDepthLevel.val)))))

def decode (bytes : List UInt8) : Option (StrategyMarketDepthMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (instrumentStatusMarker, bytes) ← InstrumentStatusMarker.decode bytes
  let (numberOfLevel, bytes) ← decodeDigits 1 bytes
  let (strategyMarketDepthLevel_, bytes) ← decodeMany StrategyMarketDepthLevel.decode numberOfLevel bytes
  if fits_strategyMarketDepthLevel : strategyMarketDepthLevel_.length < 10 ^ 1 then
    pure ({ longMessageHeader, exchangeId, symbol, instrumentStatusMarker, strategyMarketDepthLevel := ⟨strategyMarketDepthLevel_, fits_strategyMarketDepthLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyMarketDepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyMarketDepthMessage) : (encode message).length ≤ 342 := by
  have bound_strategyMarketDepthLevel := message.strategyMarketDepthLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, InstrumentStatusMarker.encode_length, encodeDigits_length, encodeMany_length_const StrategyMarketDepthLevel.encode 33 StrategyMarketDepthLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyMarketDepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentStatusMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyMarketDepthLevel.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyMarketDepthLevel.encode StrategyMarketDepthLevel.decode StrategyMarketDepthLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyMarketDepthLevel.length_lt]
  rfl

end StrategyMarketDepthMessage

/-- Option Trade Cancellation Message: 74 bytes -/
structure OptionTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace OptionTradeCancellationMessage

def encode (message : OptionTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (OptionTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, volume, tradePriceFractionPair, filler6, tradeTimestamp, filler1, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : OptionTradeCancellationMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : OptionTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OptionTradeCancellationMessage

/-- Price Fraction Pair: 8 bytes -/
structure PriceFractionPair where
  rawPrice : Alpha 7
  priceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PriceFractionPair

def encode (message : PriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPrice
    ++ (encodeUInt 1 message.priceFractionIndicator)

def decode (bytes : List UInt8) : Option (PriceFractionPair × List UInt8) := do
  let (rawPrice, bytes) ← Alpha.decode 7 bytes
  let (priceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPrice, priceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceFractionPair

/-- Future Options Trade Cancellation Message: 75 bytes -/
structure FutureOptionsTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  volume : Alpha 8
  priceFractionPair : PriceFractionPair
  priceIndicatorMarker : PriceIndicatorMarker
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler2 : Alpha 2
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FutureOptionsTradeCancellationMessage

def encode (message : FutureOptionsTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.volume
    ++ (PriceFractionPair.encode message.priceFractionPair
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (priceFractionPair, bytes) ← PriceFractionPair.decode bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, volume, priceFractionPair, priceIndicatorMarker, filler6, tradeTimestamp, filler2, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FutureOptionsTradeCancellationMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, PriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FutureOptionsTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsTradeCancellationMessage

/-- Futures Trade Cancellation Message: 64 bytes -/
structure FuturesTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCancellationMessage

def encode (message : FuturesTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePriceFractionPair, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCancellationMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCancellationMessage

/-- Strategy Trade Cancellation Message: 84 bytes -/
structure StrategyTradeCancellationMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  symbol : Alpha 30
  volume : Alpha 8
  tradePriceSign : TradePriceSign
  tradePriceFractionPair : TradePriceFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  filler1 : Alpha 1
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyTradeCancellationMessage

def encode (message : StrategyTradeCancellationMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.volume
    ++ (TradePriceSign.encode message.tradePriceSign
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.tradeNumber)))))))))

def decode (bytes : List UInt8) : Option (StrategyTradeCancellationMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceSign, bytes) ← TradePriceSign.decode bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, symbol, volume, tradePriceSign, tradePriceFractionPair, filler6, tradeTimestamp, filler1, tradeNumber }, bytes)

@[simp] theorem encode_length (message : StrategyTradeCancellationMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, TradePriceSign.encode_length, TradePriceFractionPair.encode_length]

theorem encode_length_pos (message : StrategyTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradeCancellationMessage

/-- Maximum Threshold Price Fraction Pair: 8 bytes -/
structure MaximumThresholdPriceFractionPair where
  rawMaximumThresholdPrice : Alpha 7
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFractionPair

def encode (message : MaximumThresholdPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPrice
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceFractionPair × List UInt8) := do
  let (rawMaximumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPrice, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MaximumThresholdPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaximumThresholdPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaximumThresholdPriceFractionPair

/-- Minimum Threshold Price Fraction Pair: 8 bytes -/
structure MinimumThresholdPriceFractionPair where
  rawMinimumThresholdPrice : Alpha 7
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceFractionPair

def encode (message : MinimumThresholdPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPrice
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceFractionPair × List UInt8) := do
  let (rawMinimumThresholdPrice, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPrice, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceFractionPair

/-- Tick Increment: 8 bytes -/
structure TickIncrement where
  tickIncrementNumeric : Alpha 7
  tickIncrementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickIncrement

def encode (message : TickIncrement) : List UInt8 :=
  Alpha.encode message.tickIncrementNumeric
    ++ (encodeUInt 1 message.tickIncrementFractionIndicator)

def decode (bytes : List UInt8) : Option (TickIncrement × List UInt8) := do
  let (tickIncrementNumeric, bytes) ← Alpha.decode 7 bytes
  let (tickIncrementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ tickIncrementNumeric, tickIncrementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickIncrement) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickIncrement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickIncrement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickIncrement

/-- Tick Value Fraction Pair: 8 bytes -/
structure TickValueFractionPair where
  rawTickValue : Alpha 7
  tickValueFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickValueFractionPair

def encode (message : TickValueFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickValue
    ++ (encodeUInt 1 message.tickValueFractionIndicator)

def decode (bytes : List UInt8) : Option (TickValueFractionPair × List UInt8) := do
  let (rawTickValue, bytes) ← Alpha.decode 7 bytes
  let (tickValueFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickValue, tickValueFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickValueFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickValueFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickValueFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickValueFractionPair

/-- Option Instrument Keys Message: 145 bytes -/
structure OptionInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceFractionPair : MinimumThresholdPriceFractionPair
  tickIncrement : TickIncrement
  optionType : OptionType
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  optionMarker : Alpha 2
  underlyingSymbolRoot : Alpha 12
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  deriving DecidableEq, Repr

namespace OptionInstrumentKeysMessage

def encode (message : OptionInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceFractionPair.encode message.minimumThresholdPriceFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (OptionType.encode message.optionType
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.optionMarker
    ++ (Alpha.encode message.underlyingSymbolRoot
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceFractionPair, bytes) ← MinimumThresholdPriceFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (optionType, bytes) ← OptionType.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (underlyingSymbolRoot, bytes) ← Alpha.decode 12 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceFractionPair, tickIncrement, optionType, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, optionMarker, underlyingSymbolRoot, contractSize, tickValueFractionPair, currency, deliveryType }, bytes)

@[simp] theorem encode_length (message : OptionInstrumentKeysMessage) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceFractionPair.encode_length, TickIncrement.encode_length, OptionType.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length]

theorem encode_length_pos (message : OptionInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionType.decode_encode, some_bind]
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
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [DeliveryType.decode_encode, some_bind]
  rfl

end OptionInstrumentKeysMessage

/-- Future Options Instrument Keys Message: 145 bytes -/
structure FutureOptionsInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  expiryDate : Alpha 6
  strikePriceCurrency : Alpha 3
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceFractionPair : MinimumThresholdPriceFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  deliveryType : DeliveryType
  underlyingRootSymbol : Alpha 6
  underlyingSymbolMonth : UnderlyingSymbolMonth
  underlyingSymbolYear : Alpha 2
  deriving DecidableEq, Repr

namespace FutureOptionsInstrumentKeysMessage

def encode (message : FutureOptionsInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.strikePriceCurrency
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceFractionPair.encode message.minimumThresholdPriceFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (DeliveryType.encode message.deliveryType
    ++ (Alpha.encode message.underlyingRootSymbol
    ++ (UnderlyingSymbolMonth.encode message.underlyingSymbolMonth
    ++ (Alpha.encode message.underlyingSymbolYear))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (strikePriceCurrency, bytes) ← Alpha.decode 3 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceFractionPair, bytes) ← MinimumThresholdPriceFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (underlyingRootSymbol, bytes) ← Alpha.decode 6 bytes
  let (underlyingSymbolMonth, bytes) ← UnderlyingSymbolMonth.decode bytes
  let (underlyingSymbolYear, bytes) ← Alpha.decode 2 bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, expiryDate, strikePriceCurrency, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, deliveryType, underlyingRootSymbol, underlyingSymbolMonth, underlyingSymbolYear }, bytes)

@[simp] theorem encode_length (message : FutureOptionsInstrumentKeysMessage) : (encode message).length = 145 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length, UnderlyingSymbolMonth.encode_length]

theorem encode_length_pos (message : FutureOptionsInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
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
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, UnderlyingSymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FutureOptionsInstrumentKeysMessage

/-- Underlying Instrument Keys Message: 49 bytes -/
structure UnderlyingInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  deriving DecidableEq, Repr

namespace UnderlyingInstrumentKeysMessage

def encode (message : UnderlyingInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode))))

def decode (bytes : List UInt8) : Option (UnderlyingInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  pure ({ longMessageHeader, exchangeId, groupInstrument, instrument, instrumentExternalCode }, bytes)

@[simp] theorem encode_length (message : UnderlyingInstrumentKeysMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingInstrumentKeysMessage

/-- Maximum Threshold Price Futures Fraction Pair: 8 bytes -/
structure MaximumThresholdPriceFuturesFractionPair where
  rawMaximumThresholdPriceFutures : Alpha 7
  maximumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MaximumThresholdPriceFuturesFractionPair

def encode (message : MaximumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMaximumThresholdPriceFutures
    ++ (encodeUInt 1 message.maximumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MaximumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMaximumThresholdPriceFutures, bytes) ← Alpha.decode 7 bytes
  let (maximumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMaximumThresholdPriceFutures, maximumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MaximumThresholdPriceFuturesFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MaximumThresholdPriceFuturesFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaximumThresholdPriceFuturesFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaximumThresholdPriceFuturesFractionPair

/-- Minimum Threshold Price Futures Fraction Pair: 8 bytes -/
structure MinimumThresholdPriceFuturesFractionPair where
  rawMinimumThresholdPriceFutures : Alpha 7
  minimumThresholdPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinimumThresholdPriceFuturesFractionPair

def encode (message : MinimumThresholdPriceFuturesFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinimumThresholdPriceFutures
    ++ (encodeUInt 1 message.minimumThresholdPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinimumThresholdPriceFuturesFractionPair × List UInt8) := do
  let (rawMinimumThresholdPriceFutures, bytes) ← Alpha.decode 7 bytes
  let (minimumThresholdPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinimumThresholdPriceFutures, minimumThresholdPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinimumThresholdPriceFuturesFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinimumThresholdPriceFuturesFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumThresholdPriceFuturesFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumThresholdPriceFuturesFractionPair

/-- Associated Product: 11 bytes -/
structure AssociatedProduct where
  rootSymbol : Alpha 6
  symbolMonth : SymbolMonth
  symbolYear : Alpha 2
  expiryDay : Alpha 2
  deriving DecidableEq, Repr

namespace AssociatedProduct

def encode (message : AssociatedProduct) : List UInt8 :=
  Alpha.encode message.rootSymbol
    ++ (SymbolMonth.encode message.symbolMonth
    ++ (Alpha.encode message.symbolYear
    ++ (Alpha.encode message.expiryDay)))

def decode (bytes : List UInt8) : Option (AssociatedProduct × List UInt8) := do
  let (rootSymbol, bytes) ← Alpha.decode 6 bytes
  let (symbolMonth, bytes) ← SymbolMonth.decode bytes
  let (symbolYear, bytes) ← Alpha.decode 2 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  pure ({ rootSymbol, symbolMonth, symbolYear, expiryDay }, bytes)

@[simp] theorem encode_length (message : AssociatedProduct) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SymbolMonth.encode_length]

theorem encode_length_pos (message : AssociatedProduct) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AssociatedProduct) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolMonth.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AssociatedProduct

/-- Futures Instrument Keys Message: 147 bytes -/
structure FuturesInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  expiryDate : Alpha 6
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFuturesFractionPair : MaximumThresholdPriceFuturesFractionPair
  minimumThresholdPriceFuturesFractionPair : MinimumThresholdPriceFuturesFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  contractSize : Alpha 8
  tickValueFractionPair : TickValueFractionPair
  currency : Alpha 3
  underlyingSymbol : Alpha 12
  deliveryType : DeliveryType
  associatedProduct : AssociatedProduct
  deriving DecidableEq, Repr

namespace FuturesInstrumentKeysMessage

def encode (message : FuturesInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.expiryDate
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFuturesFractionPair.encode message.maximumThresholdPriceFuturesFractionPair
    ++ (MinimumThresholdPriceFuturesFractionPair.encode message.minimumThresholdPriceFuturesFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (Alpha.encode message.contractSize
    ++ (TickValueFractionPair.encode message.tickValueFractionPair
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.underlyingSymbol
    ++ (DeliveryType.encode message.deliveryType
    ++ (AssociatedProduct.encode message.associatedProduct))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (expiryDate, bytes) ← Alpha.decode 6 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFuturesFractionPair, bytes) ← MaximumThresholdPriceFuturesFractionPair.decode bytes
  let (minimumThresholdPriceFuturesFractionPair, bytes) ← MinimumThresholdPriceFuturesFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (contractSize, bytes) ← Alpha.decode 8 bytes
  let (tickValueFractionPair, bytes) ← TickValueFractionPair.decode bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 12 bytes
  let (deliveryType, bytes) ← DeliveryType.decode bytes
  let (associatedProduct, bytes) ← AssociatedProduct.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, expiryDate, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFuturesFractionPair, minimumThresholdPriceFuturesFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, contractSize, tickValueFractionPair, currency, underlyingSymbol, deliveryType, associatedProduct }, bytes)

@[simp] theorem encode_length (message : FuturesInstrumentKeysMessage) : (encode message).length = 147 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, MaximumThresholdPriceFuturesFractionPair.encode_length, MinimumThresholdPriceFuturesFractionPair.encode_length, TickIncrement.encode_length, TickValueFractionPair.encode_length, DeliveryType.encode_length, AssociatedProduct.encode_length]

theorem encode_length_pos (message : FuturesInstrumentKeysMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaximumThresholdPriceFuturesFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFuturesFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
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
  rw [List.append_assoc, TickValueFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DeliveryType.decode_encode, some_bind]
  dsimp only
  rw [AssociatedProduct.decode_encode, some_bind]
  rfl

end FuturesInstrumentKeysMessage

/-- Strategy Instrument Leg: 35 bytes -/
structure StrategyInstrumentLeg where
  legRatioSign : LegRatioSign
  legRatio : Alpha 4
  legSymbol : Alpha 30
  deriving DecidableEq, Repr

namespace StrategyInstrumentLeg

def encode (message : StrategyInstrumentLeg) : List UInt8 :=
  LegRatioSign.encode message.legRatioSign
    ++ (Alpha.encode message.legRatio
    ++ (Alpha.encode message.legSymbol))

def decode (bytes : List UInt8) : Option (StrategyInstrumentLeg × List UInt8) := do
  let (legRatioSign, bytes) ← LegRatioSign.decode bytes
  let (legRatio, bytes) ← Alpha.decode 4 bytes
  let (legSymbol, bytes) ← Alpha.decode 30 bytes
  pure ({ legRatioSign, legRatio, legSymbol }, bytes)

@[simp] theorem encode_length (message : StrategyInstrumentLeg) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, LegRatioSign.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyInstrumentLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyInstrumentLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegRatioSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyInstrumentLeg

/-- Strategy Instrument Keys Message -/
structure StrategyInstrumentKeysMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  expiryYear : Alpha 2
  expiryMonthStrategy : Alpha 1
  expiryDay : Alpha 2
  maximumNumberOfContractsPerOrder : Alpha 6
  minimumNumberOfContractsPerOrder : Alpha 6
  maximumThresholdPriceFractionPair : MaximumThresholdPriceFractionPair
  minimumThresholdPriceFractionPair : MinimumThresholdPriceFractionPair
  tickIncrement : TickIncrement
  marketFlowIndicator : Alpha 2
  groupInstrument : Alpha 2
  instrument : Alpha 4
  instrumentExternalCode : Alpha 30
  strategyAllowImplied : StrategyAllowImplied
  strategyCode : Alpha 2
  strategyInstrumentLeg : Digited 2 StrategyInstrumentLeg
  deriving DecidableEq, Repr

namespace StrategyInstrumentKeysMessage

def encode (message : StrategyInstrumentKeysMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (Alpha.encode message.expiryYear
    ++ (Alpha.encode message.expiryMonthStrategy
    ++ (Alpha.encode message.expiryDay
    ++ (Alpha.encode message.maximumNumberOfContractsPerOrder
    ++ (Alpha.encode message.minimumNumberOfContractsPerOrder
    ++ (MaximumThresholdPriceFractionPair.encode message.maximumThresholdPriceFractionPair
    ++ (MinimumThresholdPriceFractionPair.encode message.minimumThresholdPriceFractionPair
    ++ (TickIncrement.encode message.tickIncrement
    ++ (Alpha.encode message.marketFlowIndicator
    ++ (Alpha.encode message.groupInstrument
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentExternalCode
    ++ (StrategyAllowImplied.encode message.strategyAllowImplied
    ++ (Alpha.encode message.strategyCode
    ++ (encodeDigits 2 message.strategyInstrumentLeg.val.length
    ++ (encodeMany StrategyInstrumentLeg.encode message.strategyInstrumentLeg.val))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategyInstrumentKeysMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (expiryYear, bytes) ← Alpha.decode 2 bytes
  let (expiryMonthStrategy, bytes) ← Alpha.decode 1 bytes
  let (expiryDay, bytes) ← Alpha.decode 2 bytes
  let (maximumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (minimumNumberOfContractsPerOrder, bytes) ← Alpha.decode 6 bytes
  let (maximumThresholdPriceFractionPair, bytes) ← MaximumThresholdPriceFractionPair.decode bytes
  let (minimumThresholdPriceFractionPair, bytes) ← MinimumThresholdPriceFractionPair.decode bytes
  let (tickIncrement, bytes) ← TickIncrement.decode bytes
  let (marketFlowIndicator, bytes) ← Alpha.decode 2 bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentExternalCode, bytes) ← Alpha.decode 30 bytes
  let (strategyAllowImplied, bytes) ← StrategyAllowImplied.decode bytes
  let (strategyCode, bytes) ← Alpha.decode 2 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (strategyInstrumentLeg_, bytes) ← decodeMany StrategyInstrumentLeg.decode numberOfLegs bytes
  if fits_strategyInstrumentLeg : strategyInstrumentLeg_.length < 10 ^ 2 then
    pure ({ longMessageHeader, exchangeId, strategySymbol, expiryYear, expiryMonthStrategy, expiryDay, maximumNumberOfContractsPerOrder, minimumNumberOfContractsPerOrder, maximumThresholdPriceFractionPair, minimumThresholdPriceFractionPair, tickIncrement, marketFlowIndicator, groupInstrument, instrument, instrumentExternalCode, strategyAllowImplied, strategyCode, strategyInstrumentLeg := ⟨strategyInstrumentLeg_, fits_strategyInstrumentLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyInstrumentKeysMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyInstrumentKeysMessage) : (encode message).length ≤ 3592 := by
  have bound_strategyInstrumentLeg := message.strategyInstrumentLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, MaximumThresholdPriceFractionPair.encode_length, MinimumThresholdPriceFractionPair.encode_length, TickIncrement.encode_length, StrategyAllowImplied.encode_length, encodeDigits_length, encodeMany_length_const StrategyInstrumentLeg.encode 35 StrategyInstrumentLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyInstrumentKeysMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
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
  rw [List.append_assoc, MaximumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MinimumThresholdPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TickIncrement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyAllowImplied.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.strategyInstrumentLeg.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany StrategyInstrumentLeg.encode StrategyInstrumentLeg.decode StrategyInstrumentLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyInstrumentLeg.length_lt]
  rfl

end StrategyInstrumentKeysMessage

/-- Bid Price Summary Fraction Pair: 8 bytes -/
structure BidPriceSummaryFractionPair where
  rawBidPriceSummary : Alpha 7
  bidPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace BidPriceSummaryFractionPair

def encode (message : BidPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawBidPriceSummary
    ++ (encodeUInt 1 message.bidPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (BidPriceSummaryFractionPair × List UInt8) := do
  let (rawBidPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (bidPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawBidPriceSummary, bidPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : BidPriceSummaryFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BidPriceSummaryFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPriceSummaryFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPriceSummaryFractionPair

/-- Ask Price Summary Fraction Pair: 8 bytes -/
structure AskPriceSummaryFractionPair where
  rawAskPriceSummary : Alpha 7
  askPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace AskPriceSummaryFractionPair

def encode (message : AskPriceSummaryFractionPair) : List UInt8 :=
  Alpha.encode message.rawAskPriceSummary
    ++ (encodeUInt 1 message.askPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (AskPriceSummaryFractionPair × List UInt8) := do
  let (rawAskPriceSummary, bytes) ← Alpha.decode 7 bytes
  let (askPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawAskPriceSummary, askPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : AskPriceSummaryFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AskPriceSummaryFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskPriceSummaryFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskPriceSummaryFractionPair

/-- Last Price Fraction Pair: 8 bytes -/
structure LastPriceFractionPair where
  rawLastPrice : Alpha 7
  lastPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LastPriceFractionPair

def encode (message : LastPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLastPrice
    ++ (encodeUInt 1 message.lastPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LastPriceFractionPair × List UInt8) := do
  let (rawLastPrice, bytes) ← Alpha.decode 7 bytes
  let (lastPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLastPrice, lastPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LastPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LastPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LastPriceFractionPair

/-- Open Price Fraction Pair: 8 bytes -/
structure OpenPriceFractionPair where
  rawOpenPrice : Alpha 7
  openPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpenPriceFractionPair

def encode (message : OpenPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpenPrice
    ++ (encodeUInt 1 message.openPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpenPriceFractionPair × List UInt8) := do
  let (rawOpenPrice, bytes) ← Alpha.decode 7 bytes
  let (openPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpenPrice, openPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpenPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpenPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenPriceFractionPair

/-- High Price Fraction Pair: 8 bytes -/
structure HighPriceFractionPair where
  rawHighPrice : Alpha 7
  highPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace HighPriceFractionPair

def encode (message : HighPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawHighPrice
    ++ (encodeUInt 1 message.highPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (HighPriceFractionPair × List UInt8) := do
  let (rawHighPrice, bytes) ← Alpha.decode 7 bytes
  let (highPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawHighPrice, highPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : HighPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : HighPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HighPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HighPriceFractionPair

/-- Low Price Fraction Pair: 8 bytes -/
structure LowPriceFractionPair where
  rawLowPrice : Alpha 7
  lowPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace LowPriceFractionPair

def encode (message : LowPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawLowPrice
    ++ (encodeUInt 1 message.lowPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (LowPriceFractionPair × List UInt8) := do
  let (rawLowPrice, bytes) ← Alpha.decode 7 bytes
  let (lowPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawLowPrice, lowPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : LowPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LowPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LowPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LowPriceFractionPair

/-- Settlement Price Fraction Pair: 8 bytes -/
structure SettlementPriceFractionPair where
  rawSettlementPrice : Alpha 7
  settlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementPriceFractionPair

def encode (message : SettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawSettlementPrice
    ++ (encodeUInt 1 message.settlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (SettlementPriceFractionPair × List UInt8) := do
  let (rawSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawSettlementPrice, settlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : SettlementPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SettlementPriceFractionPair

/-- Previous Settlement Price Fraction Pair: 8 bytes -/
structure PreviousSettlementPriceFractionPair where
  rawPreviousSettlementPrice : Alpha 7
  previousSettlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementPriceFractionPair

def encode (message : PreviousSettlementPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlementPrice
    ++ (encodeUInt 1 message.previousSettlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementPriceFractionPair × List UInt8) := do
  let (rawPreviousSettlementPrice, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlementPrice, previousSettlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousSettlementPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousSettlementPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousSettlementPriceFractionPair

/-- Option Summary Message: 141 bytes -/
structure OptionSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  optionSymbol : OptionSymbol
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  optionMarker : Alpha 2
  settlementPriceFractionPair : SettlementPriceFractionPair
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace OptionSummaryMessage

def encode (message : OptionSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (OptionSymbol.encode message.optionSymbol
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (Alpha.encode message.optionMarker
    ++ (SettlementPriceFractionPair.encode message.settlementPriceFractionPair
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (Reason.encode message.reason))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OptionSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (optionSymbol, bytes) ← OptionSymbol.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (optionMarker, bytes) ← Alpha.decode 2 bytes
  let (settlementPriceFractionPair, bytes) ← SettlementPriceFractionPair.decode bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ longMessageHeader, exchangeId, optionSymbol, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openInterest, openInterestDate, tick, volume, netChangeSign, netChangeFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, optionMarker, settlementPriceFractionPair, previousSettlementPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : OptionSummaryMessage) : (encode message).length = 141 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, OptionSymbol.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : OptionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end OptionSummaryMessage

/-- Opening Price Fraction Pair: 8 bytes -/
structure OpeningPriceFractionPair where
  rawOpeningPrice : Alpha 7
  openingPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace OpeningPriceFractionPair

def encode (message : OpeningPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawOpeningPrice
    ++ (encodeUInt 1 message.openingPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (OpeningPriceFractionPair × List UInt8) := do
  let (rawOpeningPrice, bytes) ← Alpha.decode 7 bytes
  let (openingPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawOpeningPrice, openingPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : OpeningPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpeningPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningPriceFractionPair

/-- Settlement Price Future Options Summary Message Fraction Pair: 8 bytes -/
structure SettlementPriceFutureOptionsSummaryMessageFractionPair where
  rawSettlementPriceFutureOptionsSummaryMessage : Alpha 7
  settlementPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace SettlementPriceFutureOptionsSummaryMessageFractionPair

def encode (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : List UInt8 :=
  Alpha.encode message.rawSettlementPriceFutureOptionsSummaryMessage
    ++ (encodeUInt 1 message.settlementPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (SettlementPriceFutureOptionsSummaryMessageFractionPair × List UInt8) := do
  let (rawSettlementPriceFutureOptionsSummaryMessage, bytes) ← Alpha.decode 7 bytes
  let (settlementPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawSettlementPriceFutureOptionsSummaryMessage, settlementPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SettlementPriceFutureOptionsSummaryMessageFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SettlementPriceFutureOptionsSummaryMessageFractionPair

/-- Future Options Summary Message: 141 bytes -/
structure FutureOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureOptionSymbol : FutureOptionSymbol
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  tick : Tick
  volume : Alpha 8
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  openingPriceFractionPair : OpeningPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  filler2 : Alpha 2
  settlementPriceFutureOptionsSummaryMessageFractionPair : SettlementPriceFutureOptionsSummaryMessageFractionPair
  previousSettlementPriceFractionPair : PreviousSettlementPriceFractionPair
  reason : Reason
  deriving DecidableEq, Repr

namespace FutureOptionsSummaryMessage

def encode (message : FutureOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureOptionSymbol.encode message.futureOptionSymbol
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Tick.encode message.tick
    ++ (Alpha.encode message.volume
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (OpeningPriceFractionPair.encode message.openingPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (Alpha.encode message.filler2
    ++ (SettlementPriceFutureOptionsSummaryMessageFractionPair.encode message.settlementPriceFutureOptionsSummaryMessageFractionPair
    ++ (PreviousSettlementPriceFractionPair.encode message.previousSettlementPriceFractionPair
    ++ (Reason.encode message.reason))))))))))))))))))))

def decode (bytes : List UInt8) : Option (FutureOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureOptionSymbol, bytes) ← FutureOptionSymbol.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (tick, bytes) ← Tick.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (openingPriceFractionPair, bytes) ← OpeningPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (settlementPriceFutureOptionsSummaryMessageFractionPair, bytes) ← SettlementPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (previousSettlementPriceFractionPair, bytes) ← PreviousSettlementPriceFractionPair.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ longMessageHeader, exchangeId, futureOptionSymbol, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openInterest, openInterestDate, tick, volume, netChangeSign, netChangeFractionPair, openingPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, filler2, settlementPriceFutureOptionsSummaryMessageFractionPair, previousSettlementPriceFractionPair, reason }, bytes)

@[simp] theorem encode_length (message : FutureOptionsSummaryMessage) : (encode message).length = 141 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureOptionSymbol.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, Tick.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, OpeningPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFutureOptionsSummaryMessageFractionPair.encode_length, PreviousSettlementPriceFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : FutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureOptionSymbol.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Tick.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpeningPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end FutureOptionsSummaryMessage

/-- Previous Settlement Fraction Pair: 8 bytes -/
structure PreviousSettlementFractionPair where
  rawPreviousSettlement : Alpha 7
  previousSettlementFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace PreviousSettlementFractionPair

def encode (message : PreviousSettlementFractionPair) : List UInt8 :=
  Alpha.encode message.rawPreviousSettlement
    ++ (encodeUInt 1 message.previousSettlementFractionIndicator)

def decode (bytes : List UInt8) : Option (PreviousSettlementFractionPair × List UInt8) := do
  let (rawPreviousSettlement, bytes) ← Alpha.decode 7 bytes
  let (previousSettlementFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawPreviousSettlement, previousSettlementFractionIndicator }, bytes)

@[simp] theorem encode_length (message : PreviousSettlementFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PreviousSettlementFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PreviousSettlementFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PreviousSettlementFractionPair

/-- External Price At Source Fraction Pair: 8 bytes -/
structure ExternalPriceAtSourceFractionPair where
  rawExternalPriceAtSource : Alpha 7
  externalPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ExternalPriceAtSourceFractionPair

def encode (message : ExternalPriceAtSourceFractionPair) : List UInt8 :=
  Alpha.encode message.rawExternalPriceAtSource
    ++ (encodeUInt 1 message.externalPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (ExternalPriceAtSourceFractionPair × List UInt8) := do
  let (rawExternalPriceAtSource, bytes) ← Alpha.decode 7 bytes
  let (externalPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawExternalPriceAtSource, externalPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : ExternalPriceAtSourceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExternalPriceAtSourceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExternalPriceAtSourceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExternalPriceAtSourceFractionPair

/-- Futures Summary Message: 137 bytes -/
structure FuturesSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceFractionPair : LastPriceFractionPair
  openPriceFractionPair : OpenPriceFractionPair
  highPriceFractionPair : HighPriceFractionPair
  lowPriceFractionPair : LowPriceFractionPair
  settlementPriceFutureOptionsSummaryMessageFractionPair : SettlementPriceFutureOptionsSummaryMessageFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  volume : Alpha 8
  previousSettlementFractionPair : PreviousSettlementFractionPair
  openInterest : Alpha 7
  openInterestDate : Alpha 6
  reason : Reason
  externalPriceAtSourceFractionPair : ExternalPriceAtSourceFractionPair
  deriving DecidableEq, Repr

namespace FuturesSummaryMessage

def encode (message : FuturesSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (SettlementPriceFutureOptionsSummaryMessageFractionPair.encode message.settlementPriceFutureOptionsSummaryMessageFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.volume
    ++ (PreviousSettlementFractionPair.encode message.previousSettlementFractionPair
    ++ (Alpha.encode message.openInterest
    ++ (Alpha.encode message.openInterestDate
    ++ (Reason.encode message.reason
    ++ (ExternalPriceAtSourceFractionPair.encode message.externalPriceAtSourceFractionPair)))))))))))))))))))

def decode (bytes : List UInt8) : Option (FuturesSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (settlementPriceFutureOptionsSummaryMessageFractionPair, bytes) ← SettlementPriceFutureOptionsSummaryMessageFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (previousSettlementFractionPair, bytes) ← PreviousSettlementFractionPair.decode bytes
  let (openInterest, bytes) ← Alpha.decode 7 bytes
  let (openInterestDate, bytes) ← Alpha.decode 6 bytes
  let (reason, bytes) ← Reason.decode bytes
  let (externalPriceAtSourceFractionPair, bytes) ← ExternalPriceAtSourceFractionPair.decode bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, bidPriceSummaryFractionPair, bidSize, askPriceSummaryFractionPair, askSize, lastPriceFractionPair, openPriceFractionPair, highPriceFractionPair, lowPriceFractionPair, settlementPriceFutureOptionsSummaryMessageFractionPair, netChangeSign, netChangeFractionPair, volume, previousSettlementFractionPair, openInterest, openInterestDate, reason, externalPriceAtSourceFractionPair }, bytes)

@[simp] theorem encode_length (message : FuturesSummaryMessage) : (encode message).length = 137 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, BidPriceSummaryFractionPair.encode_length, Alpha.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceFractionPair.encode_length, OpenPriceFractionPair.encode_length, HighPriceFractionPair.encode_length, LowPriceFractionPair.encode_length, SettlementPriceFutureOptionsSummaryMessageFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PreviousSettlementFractionPair.encode_length, Reason.encode_length, ExternalPriceAtSourceFractionPair.encode_length]

theorem encode_length_pos (message : FuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementPriceFutureOptionsSummaryMessageFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PreviousSettlementFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Reason.decode_encode, some_bind]
  dsimp only
  rw [ExternalPriceAtSourceFractionPair.decode_encode, some_bind]
  rfl

end FuturesSummaryMessage

/-- Strategy Summary Message: 125 bytes -/
structure StrategySummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  strategySymbol : Alpha 30
  bidPriceSign : BidPriceSign
  bidPriceSummaryFractionPair : BidPriceSummaryFractionPair
  bidSize : Alpha 5
  askPriceSign : AskPriceSign
  askPriceSummaryFractionPair : AskPriceSummaryFractionPair
  askSize : Alpha 5
  lastPriceSign : LastPriceSign
  lastPriceFractionPair : LastPriceFractionPair
  openPriceSign : OpenPriceSign
  openPriceFractionPair : OpenPriceFractionPair
  highPriceSign : HighPriceSign
  highPriceFractionPair : HighPriceFractionPair
  lowPriceSign : LowPriceSign
  lowPriceFractionPair : LowPriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  volume : Alpha 8
  reason : Reason
  deriving DecidableEq, Repr

namespace StrategySummaryMessage

def encode (message : StrategySummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.strategySymbol
    ++ (BidPriceSign.encode message.bidPriceSign
    ++ (BidPriceSummaryFractionPair.encode message.bidPriceSummaryFractionPair
    ++ (Alpha.encode message.bidSize
    ++ (AskPriceSign.encode message.askPriceSign
    ++ (AskPriceSummaryFractionPair.encode message.askPriceSummaryFractionPair
    ++ (Alpha.encode message.askSize
    ++ (LastPriceSign.encode message.lastPriceSign
    ++ (LastPriceFractionPair.encode message.lastPriceFractionPair
    ++ (OpenPriceSign.encode message.openPriceSign
    ++ (OpenPriceFractionPair.encode message.openPriceFractionPair
    ++ (HighPriceSign.encode message.highPriceSign
    ++ (HighPriceFractionPair.encode message.highPriceFractionPair
    ++ (LowPriceSign.encode message.lowPriceSign
    ++ (LowPriceFractionPair.encode message.lowPriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.volume
    ++ (Reason.encode message.reason))))))))))))))))))))

def decode (bytes : List UInt8) : Option (StrategySummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (strategySymbol, bytes) ← Alpha.decode 30 bytes
  let (bidPriceSign, bytes) ← BidPriceSign.decode bytes
  let (bidPriceSummaryFractionPair, bytes) ← BidPriceSummaryFractionPair.decode bytes
  let (bidSize, bytes) ← Alpha.decode 5 bytes
  let (askPriceSign, bytes) ← AskPriceSign.decode bytes
  let (askPriceSummaryFractionPair, bytes) ← AskPriceSummaryFractionPair.decode bytes
  let (askSize, bytes) ← Alpha.decode 5 bytes
  let (lastPriceSign, bytes) ← LastPriceSign.decode bytes
  let (lastPriceFractionPair, bytes) ← LastPriceFractionPair.decode bytes
  let (openPriceSign, bytes) ← OpenPriceSign.decode bytes
  let (openPriceFractionPair, bytes) ← OpenPriceFractionPair.decode bytes
  let (highPriceSign, bytes) ← HighPriceSign.decode bytes
  let (highPriceFractionPair, bytes) ← HighPriceFractionPair.decode bytes
  let (lowPriceSign, bytes) ← LowPriceSign.decode bytes
  let (lowPriceFractionPair, bytes) ← LowPriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ longMessageHeader, exchangeId, strategySymbol, bidPriceSign, bidPriceSummaryFractionPair, bidSize, askPriceSign, askPriceSummaryFractionPair, askSize, lastPriceSign, lastPriceFractionPair, openPriceSign, openPriceFractionPair, highPriceSign, highPriceFractionPair, lowPriceSign, lowPriceFractionPair, netChangeSign, netChangeFractionPair, volume, reason }, bytes)

@[simp] theorem encode_length (message : StrategySummaryMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, BidPriceSign.encode_length, BidPriceSummaryFractionPair.encode_length, AskPriceSign.encode_length, AskPriceSummaryFractionPair.encode_length, LastPriceSign.encode_length, LastPriceFractionPair.encode_length, OpenPriceSign.encode_length, OpenPriceFractionPair.encode_length, HighPriceSign.encode_length, HighPriceFractionPair.encode_length, LowPriceSign.encode_length, LowPriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, Reason.encode_length]

theorem encode_length_pos (message : StrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskPriceSummaryFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, HighPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LowPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end StrategySummaryMessage

/-- Beginning Of Options Summary Message: 13 bytes -/
structure BeginningOfOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfOptionsSummaryMessage

def encode (message : BeginningOfOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfOptionsSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfOptionsSummaryMessage

/-- Beginning Of Future Options Summary Message: 13 bytes -/
structure BeginningOfFutureOptionsSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFutureOptionsSummaryMessage

def encode (message : BeginningOfFutureOptionsSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfFutureOptionsSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFutureOptionsSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFutureOptionsSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFutureOptionsSummaryMessage

/-- Beginning Of Futures Summary Message: 13 bytes -/
structure BeginningOfFuturesSummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfFuturesSummaryMessage

def encode (message : BeginningOfFuturesSummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfFuturesSummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfFuturesSummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfFuturesSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfFuturesSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfFuturesSummaryMessage

/-- Beginning Of Strategy Summary Message: 13 bytes -/
structure BeginningOfStrategySummaryMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  deriving DecidableEq, Repr

namespace BeginningOfStrategySummaryMessage

def encode (message : BeginningOfStrategySummaryMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId)

def decode (bytes : List UInt8) : Option (BeginningOfStrategySummaryMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  pure ({ longMessageHeader, exchangeId }, bytes)

@[simp] theorem encode_length (message : BeginningOfStrategySummaryMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length]

theorem encode_length_pos (message : BeginningOfStrategySummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BeginningOfStrategySummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [ExchangeId.decode_encode, some_bind]
  rfl

end BeginningOfStrategySummaryMessage

/-- Futures Trade Correction Message: 73 bytes -/
structure FuturesTradeCorrectionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  futureProduct : FutureProduct
  volume : Alpha 8
  tradePriceFractionPair : TradePriceFractionPair
  netChangeSign : NetChangeSign
  netChangeFractionPair : NetChangeFractionPair
  filler6 : Alpha 6
  tradeTimestamp : Alpha 9
  priceIndicatorMarker : PriceIndicatorMarker
  tradeNumber : Alpha 8
  deriving DecidableEq, Repr

namespace FuturesTradeCorrectionMessage

def encode (message : FuturesTradeCorrectionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (FutureProduct.encode message.futureProduct
    ++ (Alpha.encode message.volume
    ++ (TradePriceFractionPair.encode message.tradePriceFractionPair
    ++ (NetChangeSign.encode message.netChangeSign
    ++ (NetChangeFractionPair.encode message.netChangeFractionPair
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeTimestamp
    ++ (PriceIndicatorMarker.encode message.priceIndicatorMarker
    ++ (Alpha.encode message.tradeNumber))))))))))

def decode (bytes : List UInt8) : Option (FuturesTradeCorrectionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (futureProduct, bytes) ← FutureProduct.decode bytes
  let (volume, bytes) ← Alpha.decode 8 bytes
  let (tradePriceFractionPair, bytes) ← TradePriceFractionPair.decode bytes
  let (netChangeSign, bytes) ← NetChangeSign.decode bytes
  let (netChangeFractionPair, bytes) ← NetChangeFractionPair.decode bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeTimestamp, bytes) ← Alpha.decode 9 bytes
  let (priceIndicatorMarker, bytes) ← PriceIndicatorMarker.decode bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  pure ({ longMessageHeader, exchangeId, futureProduct, volume, tradePriceFractionPair, netChangeSign, netChangeFractionPair, filler6, tradeTimestamp, priceIndicatorMarker, tradeNumber }, bytes)

@[simp] theorem encode_length (message : FuturesTradeCorrectionMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, FutureProduct.encode_length, Alpha.encode_length, TradePriceFractionPair.encode_length, NetChangeSign.encode_length, NetChangeFractionPair.encode_length, PriceIndicatorMarker.encode_length]

theorem encode_length_pos (message : FuturesTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FuturesTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FutureProduct.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradePriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NetChangeFractionPair.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceIndicatorMarker.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FuturesTradeCorrectionMessage

/-- Group Status Message: 20 bytes -/
structure GroupStatusMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  rootSymbolGroup : Alpha 6
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace GroupStatusMessage

def encode (message : GroupStatusMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.rootSymbolGroup
    ++ (GroupStatus.encode message.groupStatus)))

def decode (bytes : List UInt8) : Option (GroupStatusMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (rootSymbolGroup, bytes) ← Alpha.decode 6 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ longMessageHeader, exchangeId, rootSymbolGroup, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end GroupStatusMessage

/-- Group Status Strategies Message: 16 bytes -/
structure GroupStatusStrategiesMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  groupInstrument : Alpha 2
  groupStatus : GroupStatus
  deriving DecidableEq, Repr

namespace GroupStatusStrategiesMessage

def encode (message : GroupStatusStrategiesMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.groupInstrument
    ++ (GroupStatus.encode message.groupStatus)))

def decode (bytes : List UInt8) : Option (GroupStatusStrategiesMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (groupInstrument, bytes) ← Alpha.decode 2 bytes
  let (groupStatus, bytes) ← GroupStatus.decode bytes
  pure ({ longMessageHeader, exchangeId, groupInstrument, groupStatus }, bytes)

@[simp] theorem encode_length (message : GroupStatusStrategiesMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, GroupStatus.encode_length]

theorem encode_length_pos (message : GroupStatusStrategiesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStatusStrategiesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GroupStatus.decode_encode, some_bind]
  rfl

end GroupStatusStrategiesMessage

/-- Regular Text Bulletin: 80 bytes -/
structure RegularTextBulletin where
  regularBulletinContents : Alpha 79
  continueMarker : ContinueMarker
  deriving DecidableEq, Repr

namespace RegularTextBulletin

def encode (message : RegularTextBulletin) : List UInt8 :=
  Alpha.encode message.regularBulletinContents
    ++ (ContinueMarker.encode message.continueMarker)

def decode (bytes : List UInt8) : Option (RegularTextBulletin × List UInt8) := do
  let (regularBulletinContents, bytes) ← Alpha.decode 79 bytes
  let (continueMarker, bytes) ← ContinueMarker.decode bytes
  pure ({ regularBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : RegularTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ContinueMarker.encode_length]

theorem encode_length_pos (message : RegularTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegularTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ContinueMarker.decode_encode, some_bind]
  rfl

end RegularTextBulletin

/-- Special Text Bulletin: 80 bytes -/
structure SpecialTextBulletin where
  symbol : Alpha 30
  specialBulletinContents : Alpha 49
  continueMarker : ContinueMarker
  deriving DecidableEq, Repr

namespace SpecialTextBulletin

def encode (message : SpecialTextBulletin) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.specialBulletinContents
    ++ (ContinueMarker.encode message.continueMarker))

def decode (bytes : List UInt8) : Option (SpecialTextBulletin × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 30 bytes
  let (specialBulletinContents, bytes) ← Alpha.decode 49 bytes
  let (continueMarker, bytes) ← ContinueMarker.decode bytes
  pure ({ symbol, specialBulletinContents, continueMarker }, bytes)

@[simp] theorem encode_length (message : SpecialTextBulletin) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ContinueMarker.encode_length]

theorem encode_length_pos (message : SpecialTextBulletin) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialTextBulletin) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ContinueMarker.decode_encode, some_bind]
  rfl

end SpecialTextBulletin

/-- Any Bulletin, selected by Bulletin Type -/
inductive Bulletin where
  | regularTextBulletin (message : RegularTextBulletin) -- "1" 0x31
  | specialTextBulletin (message : SpecialTextBulletin) -- "2" 0x32
  deriving DecidableEq, Repr

namespace Bulletin

/-- The Bulletin Type each message is sent under -/
def tag : Bulletin → BitVec 8
  | .regularTextBulletin _ => 49
  | .specialTextBulletin _ => 50

def encode : Bulletin → List UInt8
  | .regularTextBulletin message => RegularTextBulletin.encode message
  | .specialTextBulletin message => SpecialTextBulletin.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Bulletin) : (encode message).length ≤ 80 := by
  cases message with
  | regularTextBulletin inner =>
    simp only [encode, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [encode, SpecialTextBulletin.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Bulletin × List UInt8) :=
  if tag = 49 then (RegularTextBulletin.decode bytes).map fun (message, rest) => (.regularTextBulletin message, rest)
  else if tag = 50 then (SpecialTextBulletin.decode bytes).map fun (message, rest) => (.specialTextBulletin message, rest)
  else none

@[simp] theorem decode_encode (message : Bulletin) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Bulletin

/-- Bulletins Message -/
structure BulletinsMessage where
  longMessageHeader : LongMessageHeader
  reserved : Alpha 1
  bulletin : Bulletin
  deriving DecidableEq, Repr

namespace BulletinsMessage

def encode (message : BulletinsMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.reserved
    ++ (encodeUInt 1 (Bulletin.tag message.bulletin)
    ++ (Bulletin.encode message.bulletin)))

def decode (bytes : List UInt8) : Option (BulletinsMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (bulletinType, bytes) ← decodeUInt 1 bytes
  let (bulletin, bytes) ← Bulletin.decode bulletinType bytes
  pure ({ longMessageHeader, reserved, bulletin }, bytes)

theorem encode_length_pos (message : BulletinsMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulletinsMessage) : (encode message).length ≤ 94 := by
  unfold encode
  cases message.bulletin with
  | regularTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeUInt_length, RegularTextBulletin.encode_length]
    omega
  | specialTextBulletin inner =>
    simp only [Bulletin.encode, List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, Alpha.encode_length, encodeUInt_length, SpecialTextBulletin.encode_length]
    omega

@[simp] theorem decode_encode (message : BulletinsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Bulletin.decode_encode, some_bind]
  rfl

end BulletinsMessage

/-- End Of Sales Message: 19 bytes -/
structure EndOfSalesMessage where
  longMessageHeader : LongMessageHeader
  reserved : Alpha 1
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfSalesMessage

def encode (message : EndOfSalesMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.reserved
    ++ (Alpha.encode message.time))

def decode (bytes : List UInt8) : Option (EndOfSalesMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (reserved, bytes) ← Alpha.decode 1 bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, reserved, time }, bytes)

@[simp] theorem encode_length (message : EndOfSalesMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfSalesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSalesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSalesMessage

/-- Min Price Fraction Pair: 8 bytes -/
structure MinPriceFractionPair where
  rawMinPrice : Alpha 7
  minPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace MinPriceFractionPair

def encode (message : MinPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawMinPrice
    ++ (encodeUInt 1 message.minPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (MinPriceFractionPair × List UInt8) := do
  let (rawMinPrice, bytes) ← Alpha.decode 7 bytes
  let (minPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawMinPrice, minPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : MinPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MinPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinPriceFractionPair

/-- Tick Price Fraction Pair: 8 bytes -/
structure TickPriceFractionPair where
  rawTickPrice : Alpha 7
  tickPriceFractionIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace TickPriceFractionPair

def encode (message : TickPriceFractionPair) : List UInt8 :=
  Alpha.encode message.rawTickPrice
    ++ (encodeUInt 1 message.tickPriceFractionIndicator)

def decode (bytes : List UInt8) : Option (TickPriceFractionPair × List UInt8) := do
  let (rawTickPrice, bytes) ← Alpha.decode 7 bytes
  let (tickPriceFractionIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ rawTickPrice, tickPriceFractionIndicator }, bytes)

@[simp] theorem encode_length (message : TickPriceFractionPair) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickPriceFractionPair) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickPriceFractionPair) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickPriceFractionPair

/-- Tick Entry: 16 bytes -/
structure TickEntry where
  minPriceFractionPair : MinPriceFractionPair
  tickPriceFractionPair : TickPriceFractionPair
  deriving DecidableEq, Repr

namespace TickEntry

def encode (message : TickEntry) : List UInt8 :=
  MinPriceFractionPair.encode message.minPriceFractionPair
    ++ (TickPriceFractionPair.encode message.tickPriceFractionPair)

def decode (bytes : List UInt8) : Option (TickEntry × List UInt8) := do
  let (minPriceFractionPair, bytes) ← MinPriceFractionPair.decode bytes
  let (tickPriceFractionPair, bytes) ← TickPriceFractionPair.decode bytes
  pure ({ minPriceFractionPair, tickPriceFractionPair }, bytes)

@[simp] theorem encode_length (message : TickEntry) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, MinPriceFractionPair.encode_length, TickPriceFractionPair.encode_length]

theorem encode_length_pos (message : TickEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MinPriceFractionPair.decode_encode, some_bind]
  dsimp only
  rw [TickPriceFractionPair.decode_encode, some_bind]
  rfl

end TickEntry

/-- Tick Table Message -/
structure TickTableMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  tickTableName : Alpha 50
  tickTableShortName : Alpha 2
  tickEntry : Digited 2 TickEntry
  deriving DecidableEq, Repr

namespace TickTableMessage

def encode (message : TickTableMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.tickTableName
    ++ (Alpha.encode message.tickTableShortName
    ++ (encodeDigits 2 message.tickEntry.val.length
    ++ (encodeMany TickEntry.encode message.tickEntry.val)))))

def decode (bytes : List UInt8) : Option (TickTableMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (tickTableName, bytes) ← Alpha.decode 50 bytes
  let (tickTableShortName, bytes) ← Alpha.decode 2 bytes
  let (nbEntries, bytes) ← decodeDigits 2 bytes
  let (tickEntry_, bytes) ← decodeMany TickEntry.decode nbEntries bytes
  if fits_tickEntry : tickEntry_.length < 10 ^ 2 then
    pure ({ longMessageHeader, exchangeId, tickTableName, tickTableShortName, tickEntry := ⟨tickEntry_, fits_tickEntry⟩ }, bytes)
  else none

theorem encode_length_pos (message : TickTableMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [LongMessageHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickTableMessage) : (encode message).length ≤ 1651 := by
  have bound_tickEntry := message.tickEntry.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const TickEntry.encode 16 TickEntry.encode_length]
  omega

@[simp] theorem decode_encode (message : TickTableMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.tickEntry.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany TickEntry.encode TickEntry.decode TickEntry.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tickEntry.length_lt]
  rfl

end TickTableMessage

/-- End Of Transmission Message: 19 bytes -/
structure EndOfTransmissionMessage where
  longMessageHeader : LongMessageHeader
  exchangeId : ExchangeId
  time : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmissionMessage

def encode (message : EndOfTransmissionMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (ExchangeId.encode message.exchangeId
    ++ (Alpha.encode message.time))

def decode (bytes : List UInt8) : Option (EndOfTransmissionMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (exchangeId, bytes) ← ExchangeId.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, exchangeId, time }, bytes)

@[simp] theorem encode_length (message : EndOfTransmissionMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, ExchangeId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmissionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExchangeId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmissionMessage

/-- Circuit Assurance Message: 18 bytes -/
structure CircuitAssuranceMessage where
  longMessageHeader : LongMessageHeader
  time : Alpha 6
  deriving DecidableEq, Repr

namespace CircuitAssuranceMessage

def encode (message : CircuitAssuranceMessage) : List UInt8 :=
  LongMessageHeader.encode message.longMessageHeader
    ++ (Alpha.encode message.time)

def decode (bytes : List UInt8) : Option (CircuitAssuranceMessage × List UInt8) := do
  let (longMessageHeader, bytes) ← LongMessageHeader.decode bytes
  let (time, bytes) ← Alpha.decode 6 bytes
  pure ({ longMessageHeader, time }, bytes)

@[simp] theorem encode_length (message : CircuitAssuranceMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, LongMessageHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CircuitAssuranceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CircuitAssuranceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LongMessageHeader.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CircuitAssuranceMessage

/-- Any Message Body, selected by Message Type -/
inductive MessageBody where
  | optionTradeMessage (message : OptionTradeMessage) -- "C " 0x4320
  | futureOptionsTradeMessage (message : FutureOptionsTradeMessage) -- "CB" 0x4342
  | futuresTradeMessage (message : FuturesTradeMessage) -- "CF" 0x4346
  | strategyTradeMessage (message : StrategyTradeMessage) -- "CS" 0x4353
  | optionRequestForQuoteRfqMessage (message : OptionRequestForQuoteRfqMessage) -- "D " 0x4420
  | futureOptionsRequestForQuoteRfqMessage (message : FutureOptionsRequestForQuoteRfqMessage) -- "DB" 0x4442
  | futuresRequestForQuoteRfqMessage (message : FuturesRequestForQuoteRfqMessage) -- "DF" 0x4446
  | strategyRequestForQuoteRfqMessage (message : StrategyRequestForQuoteRfqMessage) -- "DS" 0x4453
  | instrumentScheduleNoticeOptionMessage (message : InstrumentScheduleNoticeOptionMessage) -- "E " 0x4520
  | instrumentScheduleNoticeFuturesOptionMessage (message : InstrumentScheduleNoticeFuturesOptionMessage) -- "EB" 0x4542
  | instrumentScheduleNoticeFutureMessage (message : InstrumentScheduleNoticeFutureMessage) -- "EF" 0x4546
  | instrumentScheduleNoticeStrategyMessage (message : InstrumentScheduleNoticeStrategyMessage) -- "ES" 0x4553
  | optionQuoteMessage (message : OptionQuoteMessage) -- "F " 0x4620
  | futureOptionsQuoteMessage (message : FutureOptionsQuoteMessage) -- "FB" 0x4642
  | futuresQuoteMessage (message : FuturesQuoteMessage) -- "FF" 0x4646
  | strategyQuoteMessage (message : StrategyQuoteMessage) -- "FS" 0x4653
  | optionMarketDepthMessage (message : OptionMarketDepthMessage) -- "H " 0x4820
  | futureOptionsMarketDepthMessage (message : FutureOptionsMarketDepthMessage) -- "HB" 0x4842
  | futuresMarketDepthMessage (message : FuturesMarketDepthMessage) -- "HF" 0x4846
  | strategyMarketDepthMessage (message : StrategyMarketDepthMessage) -- "HS" 0x4853
  | optionTradeCancellationMessage (message : OptionTradeCancellationMessage) -- "I " 0x4920
  | futureOptionsTradeCancellationMessage (message : FutureOptionsTradeCancellationMessage) -- "IB" 0x4942
  | futuresTradeCancellationMessage (message : FuturesTradeCancellationMessage) -- "IF" 0x4946
  | strategyTradeCancellationMessage (message : StrategyTradeCancellationMessage) -- "IS" 0x4953
  | optionInstrumentKeysMessage (message : OptionInstrumentKeysMessage) -- "J " 0x4A20
  | futureOptionsInstrumentKeysMessage (message : FutureOptionsInstrumentKeysMessage) -- "JB" 0x4A42
  | underlyingInstrumentKeysMessage (message : UnderlyingInstrumentKeysMessage) -- "JE" 0x4A45
  | futuresInstrumentKeysMessage (message : FuturesInstrumentKeysMessage) -- "JF" 0x4A46
  | strategyInstrumentKeysMessage (message : StrategyInstrumentKeysMessage) -- "JS" 0x4A53
  | optionSummaryMessage (message : OptionSummaryMessage) -- "N " 0x4E20
  | futureOptionsSummaryMessage (message : FutureOptionsSummaryMessage) -- "NB" 0x4E42
  | futuresSummaryMessage (message : FuturesSummaryMessage) -- "NF" 0x4E46
  | strategySummaryMessage (message : StrategySummaryMessage) -- "NS" 0x4E53
  | beginningOfOptionsSummaryMessage (message : BeginningOfOptionsSummaryMessage) -- "Q " 0x5120
  | beginningOfFutureOptionsSummaryMessage (message : BeginningOfFutureOptionsSummaryMessage) -- "QB" 0x5142
  | beginningOfFuturesSummaryMessage (message : BeginningOfFuturesSummaryMessage) -- "QF" 0x5146
  | beginningOfStrategySummaryMessage (message : BeginningOfStrategySummaryMessage) -- "QS" 0x5153
  | futuresTradeCorrectionMessage (message : FuturesTradeCorrectionMessage) -- "XF" 0x5846
  | groupStatusMessage (message : GroupStatusMessage) -- "GR" 0x4752
  | groupStatusStrategiesMessage (message : GroupStatusStrategiesMessage) -- "GS" 0x4753
  | bulletinsMessage (message : BulletinsMessage) -- "L " 0x4C20
  | endOfSalesMessage (message : EndOfSalesMessage) -- "S " 0x5320
  | tickTableMessage (message : TickTableMessage) -- "TT" 0x5454
  | endOfTransmissionMessage (message : EndOfTransmissionMessage) -- "U " 0x5520
  | circuitAssuranceMessage (message : CircuitAssuranceMessage) -- "V " 0x5620
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Type each message is sent under -/
def tag : MessageBody → BitVec 16
  | .optionTradeMessage _ => 17184
  | .futureOptionsTradeMessage _ => 17218
  | .futuresTradeMessage _ => 17222
  | .strategyTradeMessage _ => 17235
  | .optionRequestForQuoteRfqMessage _ => 17440
  | .futureOptionsRequestForQuoteRfqMessage _ => 17474
  | .futuresRequestForQuoteRfqMessage _ => 17478
  | .strategyRequestForQuoteRfqMessage _ => 17491
  | .instrumentScheduleNoticeOptionMessage _ => 17696
  | .instrumentScheduleNoticeFuturesOptionMessage _ => 17730
  | .instrumentScheduleNoticeFutureMessage _ => 17734
  | .instrumentScheduleNoticeStrategyMessage _ => 17747
  | .optionQuoteMessage _ => 17952
  | .futureOptionsQuoteMessage _ => 17986
  | .futuresQuoteMessage _ => 17990
  | .strategyQuoteMessage _ => 18003
  | .optionMarketDepthMessage _ => 18464
  | .futureOptionsMarketDepthMessage _ => 18498
  | .futuresMarketDepthMessage _ => 18502
  | .strategyMarketDepthMessage _ => 18515
  | .optionTradeCancellationMessage _ => 18720
  | .futureOptionsTradeCancellationMessage _ => 18754
  | .futuresTradeCancellationMessage _ => 18758
  | .strategyTradeCancellationMessage _ => 18771
  | .optionInstrumentKeysMessage _ => 18976
  | .futureOptionsInstrumentKeysMessage _ => 19010
  | .underlyingInstrumentKeysMessage _ => 19013
  | .futuresInstrumentKeysMessage _ => 19014
  | .strategyInstrumentKeysMessage _ => 19027
  | .optionSummaryMessage _ => 20000
  | .futureOptionsSummaryMessage _ => 20034
  | .futuresSummaryMessage _ => 20038
  | .strategySummaryMessage _ => 20051
  | .beginningOfOptionsSummaryMessage _ => 20768
  | .beginningOfFutureOptionsSummaryMessage _ => 20802
  | .beginningOfFuturesSummaryMessage _ => 20806
  | .beginningOfStrategySummaryMessage _ => 20819
  | .futuresTradeCorrectionMessage _ => 22598
  | .groupStatusMessage _ => 18258
  | .groupStatusStrategiesMessage _ => 18259
  | .bulletinsMessage _ => 19488
  | .endOfSalesMessage _ => 21280
  | .tickTableMessage _ => 21588
  | .endOfTransmissionMessage _ => 21792
  | .circuitAssuranceMessage _ => 22048

def encode : MessageBody → List UInt8
  | .optionTradeMessage message => OptionTradeMessage.encode message
  | .futureOptionsTradeMessage message => FutureOptionsTradeMessage.encode message
  | .futuresTradeMessage message => FuturesTradeMessage.encode message
  | .strategyTradeMessage message => StrategyTradeMessage.encode message
  | .optionRequestForQuoteRfqMessage message => OptionRequestForQuoteRfqMessage.encode message
  | .futureOptionsRequestForQuoteRfqMessage message => FutureOptionsRequestForQuoteRfqMessage.encode message
  | .futuresRequestForQuoteRfqMessage message => FuturesRequestForQuoteRfqMessage.encode message
  | .strategyRequestForQuoteRfqMessage message => StrategyRequestForQuoteRfqMessage.encode message
  | .instrumentScheduleNoticeOptionMessage message => InstrumentScheduleNoticeOptionMessage.encode message
  | .instrumentScheduleNoticeFuturesOptionMessage message => InstrumentScheduleNoticeFuturesOptionMessage.encode message
  | .instrumentScheduleNoticeFutureMessage message => InstrumentScheduleNoticeFutureMessage.encode message
  | .instrumentScheduleNoticeStrategyMessage message => InstrumentScheduleNoticeStrategyMessage.encode message
  | .optionQuoteMessage message => OptionQuoteMessage.encode message
  | .futureOptionsQuoteMessage message => FutureOptionsQuoteMessage.encode message
  | .futuresQuoteMessage message => FuturesQuoteMessage.encode message
  | .strategyQuoteMessage message => StrategyQuoteMessage.encode message
  | .optionMarketDepthMessage message => OptionMarketDepthMessage.encode message
  | .futureOptionsMarketDepthMessage message => FutureOptionsMarketDepthMessage.encode message
  | .futuresMarketDepthMessage message => FuturesMarketDepthMessage.encode message
  | .strategyMarketDepthMessage message => StrategyMarketDepthMessage.encode message
  | .optionTradeCancellationMessage message => OptionTradeCancellationMessage.encode message
  | .futureOptionsTradeCancellationMessage message => FutureOptionsTradeCancellationMessage.encode message
  | .futuresTradeCancellationMessage message => FuturesTradeCancellationMessage.encode message
  | .strategyTradeCancellationMessage message => StrategyTradeCancellationMessage.encode message
  | .optionInstrumentKeysMessage message => OptionInstrumentKeysMessage.encode message
  | .futureOptionsInstrumentKeysMessage message => FutureOptionsInstrumentKeysMessage.encode message
  | .underlyingInstrumentKeysMessage message => UnderlyingInstrumentKeysMessage.encode message
  | .futuresInstrumentKeysMessage message => FuturesInstrumentKeysMessage.encode message
  | .strategyInstrumentKeysMessage message => StrategyInstrumentKeysMessage.encode message
  | .optionSummaryMessage message => OptionSummaryMessage.encode message
  | .futureOptionsSummaryMessage message => FutureOptionsSummaryMessage.encode message
  | .futuresSummaryMessage message => FuturesSummaryMessage.encode message
  | .strategySummaryMessage message => StrategySummaryMessage.encode message
  | .beginningOfOptionsSummaryMessage message => BeginningOfOptionsSummaryMessage.encode message
  | .beginningOfFutureOptionsSummaryMessage message => BeginningOfFutureOptionsSummaryMessage.encode message
  | .beginningOfFuturesSummaryMessage message => BeginningOfFuturesSummaryMessage.encode message
  | .beginningOfStrategySummaryMessage message => BeginningOfStrategySummaryMessage.encode message
  | .futuresTradeCorrectionMessage message => FuturesTradeCorrectionMessage.encode message
  | .groupStatusMessage message => GroupStatusMessage.encode message
  | .groupStatusStrategiesMessage message => GroupStatusStrategiesMessage.encode message
  | .bulletinsMessage message => BulletinsMessage.encode message
  | .endOfSalesMessage message => EndOfSalesMessage.encode message
  | .tickTableMessage message => TickTableMessage.encode message
  | .endOfTransmissionMessage message => EndOfTransmissionMessage.encode message
  | .circuitAssuranceMessage message => CircuitAssuranceMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 3592 := by
  cases message with
  | optionTradeMessage inner =>
    simp only [encode, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [encode, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [encode, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [encode, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteRfqMessage inner =>
    simp only [encode, OptionRequestForQuoteRfqMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteRfqMessage inner =>
    simp only [encode, FutureOptionsRequestForQuoteRfqMessage.encode_length]
    omega
  | futuresRequestForQuoteRfqMessage inner =>
    simp only [encode, FuturesRequestForQuoteRfqMessage.encode_length]
    omega
  | strategyRequestForQuoteRfqMessage inner =>
    simp only [encode, StrategyRequestForQuoteRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [encode, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [encode, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [encode, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [encode, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [encode, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [encode, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [encode, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [encode, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [encode, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [encode, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [encode, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [encode, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [encode, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [encode, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [encode]
    omega
  | optionSummaryMessage inner =>
    simp only [encode, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [encode, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [encode, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [encode, StrategySummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [encode, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [encode, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [encode, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [encode, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [encode, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [encode, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfSalesMessage inner =>
    simp only [encode, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [encode]
    omega
  | endOfTransmissionMessage inner =>
    simp only [encode, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [encode, CircuitAssuranceMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 17184 then (OptionTradeMessage.decode bytes).map fun (message, rest) => (.optionTradeMessage message, rest)
  else if tag = 17218 then (FutureOptionsTradeMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeMessage message, rest)
  else if tag = 17222 then (FuturesTradeMessage.decode bytes).map fun (message, rest) => (.futuresTradeMessage message, rest)
  else if tag = 17235 then (StrategyTradeMessage.decode bytes).map fun (message, rest) => (.strategyTradeMessage message, rest)
  else if tag = 17440 then (OptionRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.optionRequestForQuoteRfqMessage message, rest)
  else if tag = 17474 then (FutureOptionsRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.futureOptionsRequestForQuoteRfqMessage message, rest)
  else if tag = 17478 then (FuturesRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.futuresRequestForQuoteRfqMessage message, rest)
  else if tag = 17491 then (StrategyRequestForQuoteRfqMessage.decode bytes).map fun (message, rest) => (.strategyRequestForQuoteRfqMessage message, rest)
  else if tag = 17696 then (InstrumentScheduleNoticeOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeOptionMessage message, rest)
  else if tag = 17730 then (InstrumentScheduleNoticeFuturesOptionMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFuturesOptionMessage message, rest)
  else if tag = 17734 then (InstrumentScheduleNoticeFutureMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeFutureMessage message, rest)
  else if tag = 17747 then (InstrumentScheduleNoticeStrategyMessage.decode bytes).map fun (message, rest) => (.instrumentScheduleNoticeStrategyMessage message, rest)
  else if tag = 17952 then (OptionQuoteMessage.decode bytes).map fun (message, rest) => (.optionQuoteMessage message, rest)
  else if tag = 17986 then (FutureOptionsQuoteMessage.decode bytes).map fun (message, rest) => (.futureOptionsQuoteMessage message, rest)
  else if tag = 17990 then (FuturesQuoteMessage.decode bytes).map fun (message, rest) => (.futuresQuoteMessage message, rest)
  else if tag = 18003 then (StrategyQuoteMessage.decode bytes).map fun (message, rest) => (.strategyQuoteMessage message, rest)
  else if tag = 18464 then (OptionMarketDepthMessage.decode bytes).map fun (message, rest) => (.optionMarketDepthMessage message, rest)
  else if tag = 18498 then (FutureOptionsMarketDepthMessage.decode bytes).map fun (message, rest) => (.futureOptionsMarketDepthMessage message, rest)
  else if tag = 18502 then (FuturesMarketDepthMessage.decode bytes).map fun (message, rest) => (.futuresMarketDepthMessage message, rest)
  else if tag = 18515 then (StrategyMarketDepthMessage.decode bytes).map fun (message, rest) => (.strategyMarketDepthMessage message, rest)
  else if tag = 18720 then (OptionTradeCancellationMessage.decode bytes).map fun (message, rest) => (.optionTradeCancellationMessage message, rest)
  else if tag = 18754 then (FutureOptionsTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futureOptionsTradeCancellationMessage message, rest)
  else if tag = 18758 then (FuturesTradeCancellationMessage.decode bytes).map fun (message, rest) => (.futuresTradeCancellationMessage message, rest)
  else if tag = 18771 then (StrategyTradeCancellationMessage.decode bytes).map fun (message, rest) => (.strategyTradeCancellationMessage message, rest)
  else if tag = 18976 then (OptionInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.optionInstrumentKeysMessage message, rest)
  else if tag = 19010 then (FutureOptionsInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futureOptionsInstrumentKeysMessage message, rest)
  else if tag = 19013 then (UnderlyingInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.underlyingInstrumentKeysMessage message, rest)
  else if tag = 19014 then (FuturesInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.futuresInstrumentKeysMessage message, rest)
  else if tag = 19027 then (StrategyInstrumentKeysMessage.decode bytes).map fun (message, rest) => (.strategyInstrumentKeysMessage message, rest)
  else if tag = 20000 then (OptionSummaryMessage.decode bytes).map fun (message, rest) => (.optionSummaryMessage message, rest)
  else if tag = 20034 then (FutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.futureOptionsSummaryMessage message, rest)
  else if tag = 20038 then (FuturesSummaryMessage.decode bytes).map fun (message, rest) => (.futuresSummaryMessage message, rest)
  else if tag = 20051 then (StrategySummaryMessage.decode bytes).map fun (message, rest) => (.strategySummaryMessage message, rest)
  else if tag = 20768 then (BeginningOfOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfOptionsSummaryMessage message, rest)
  else if tag = 20802 then (BeginningOfFutureOptionsSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFutureOptionsSummaryMessage message, rest)
  else if tag = 20806 then (BeginningOfFuturesSummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfFuturesSummaryMessage message, rest)
  else if tag = 20819 then (BeginningOfStrategySummaryMessage.decode bytes).map fun (message, rest) => (.beginningOfStrategySummaryMessage message, rest)
  else if tag = 22598 then (FuturesTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.futuresTradeCorrectionMessage message, rest)
  else if tag = 18258 then (GroupStatusMessage.decode bytes).map fun (message, rest) => (.groupStatusMessage message, rest)
  else if tag = 18259 then (GroupStatusStrategiesMessage.decode bytes).map fun (message, rest) => (.groupStatusStrategiesMessage message, rest)
  else if tag = 19488 then (BulletinsMessage.decode bytes).map fun (message, rest) => (.bulletinsMessage message, rest)
  else if tag = 21280 then (EndOfSalesMessage.decode bytes).map fun (message, rest) => (.endOfSalesMessage message, rest)
  else if tag = 21588 then (TickTableMessage.decode bytes).map fun (message, rest) => (.tickTableMessage message, rest)
  else if tag = 21792 then (EndOfTransmissionMessage.decode bytes).map fun (message, rest) => (.endOfTransmissionMessage message, rest)
  else if tag = 22048 then (CircuitAssuranceMessage.decode bytes).map fun (message, rest) => (.circuitAssuranceMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Sola Frame -/
structure SolaFrame where
  solaMessageStart : BitVec 8
  sequenceNumber : Alpha 9
  messageBody : MessageBody
  solaMessageEnd : BitVec 8
  deriving DecidableEq, Repr

namespace SolaFrame

def encode (message : SolaFrame) : List UInt8 :=
  encodeUInt 1 message.solaMessageStart
    ++ (Alpha.encode message.sequenceNumber
    ++ (encodeUInt 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody
    ++ (encodeUInt 1 message.solaMessageEnd))))

def decode (bytes : List UInt8) : Option (SolaFrame × List UInt8) := do
  let (solaMessageStart, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 9 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageType bytes
  let (solaMessageEnd, bytes) ← decodeUInt 1 bytes
  pure ({ solaMessageStart, sequenceNumber, messageBody, solaMessageEnd }, bytes)

theorem encode_length_pos (message : SolaFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SolaFrame) : (encode message).length ≤ 3605 := by
  unfold encode
  cases message.messageBody with
  | optionTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeMessage.encode_length]
    omega
  | futureOptionsTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeMessage.encode_length]
    omega
  | futuresTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeMessage.encode_length]
    omega
  | strategyTradeMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeMessage.encode_length]
    omega
  | optionRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionRequestForQuoteRfqMessage.encode_length]
    omega
  | futureOptionsRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsRequestForQuoteRfqMessage.encode_length]
    omega
  | futuresRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesRequestForQuoteRfqMessage.encode_length]
    omega
  | strategyRequestForQuoteRfqMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyRequestForQuoteRfqMessage.encode_length]
    omega
  | instrumentScheduleNoticeOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFuturesOptionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFuturesOptionMessage.encode_length]
    omega
  | instrumentScheduleNoticeFutureMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeFutureMessage.encode_length]
    omega
  | instrumentScheduleNoticeStrategyMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, InstrumentScheduleNoticeStrategyMessage.encode_length]
    omega
  | optionQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionQuoteMessage.encode_length]
    omega
  | futureOptionsQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsQuoteMessage.encode_length]
    omega
  | futuresQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesQuoteMessage.encode_length]
    omega
  | strategyQuoteMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyQuoteMessage.encode_length]
    omega
  | optionMarketDepthMessage inner =>
    have bound_inner := OptionMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futureOptionsMarketDepthMessage inner =>
    have bound_inner := FutureOptionsMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | futuresMarketDepthMessage inner =>
    have bound_inner := FuturesMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | strategyMarketDepthMessage inner =>
    have bound_inner := StrategyMarketDepthMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionTradeCancellationMessage.encode_length]
    omega
  | futureOptionsTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsTradeCancellationMessage.encode_length]
    omega
  | futuresTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCancellationMessage.encode_length]
    omega
  | strategyTradeCancellationMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategyTradeCancellationMessage.encode_length]
    omega
  | optionInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionInstrumentKeysMessage.encode_length]
    omega
  | futureOptionsInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsInstrumentKeysMessage.encode_length]
    omega
  | underlyingInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, UnderlyingInstrumentKeysMessage.encode_length]
    omega
  | futuresInstrumentKeysMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesInstrumentKeysMessage.encode_length]
    omega
  | strategyInstrumentKeysMessage inner =>
    have bound_inner := StrategyInstrumentKeysMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | optionSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OptionSummaryMessage.encode_length]
    omega
  | futureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FutureOptionsSummaryMessage.encode_length]
    omega
  | futuresSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesSummaryMessage.encode_length]
    omega
  | strategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, StrategySummaryMessage.encode_length]
    omega
  | beginningOfOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFutureOptionsSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFutureOptionsSummaryMessage.encode_length]
    omega
  | beginningOfFuturesSummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfFuturesSummaryMessage.encode_length]
    omega
  | beginningOfStrategySummaryMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, BeginningOfStrategySummaryMessage.encode_length]
    omega
  | futuresTradeCorrectionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, FuturesTradeCorrectionMessage.encode_length]
    omega
  | groupStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusMessage.encode_length]
    omega
  | groupStatusStrategiesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, GroupStatusStrategiesMessage.encode_length]
    omega
  | bulletinsMessage inner =>
    have bound_inner := BulletinsMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfSalesMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfSalesMessage.encode_length]
    omega
  | tickTableMessage inner =>
    have bound_inner := TickTableMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | endOfTransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, EndOfTransmissionMessage.encode_length]
    omega
  | circuitAssuranceMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, CircuitAssuranceMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SolaFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SolaFrame

/-- Packet -/
structure Packet where
  solaFrame : List SolaFrame
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SolaFrame.encode message.solaFrame

def decode (bytes : List UInt8) : Option Packet := do
  let solaFrame ← decodeAll SolaFrame.decode bytes.length bytes
  pure { solaFrame }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SolaFrame.encode SolaFrame.decode SolaFrame.decode_encode SolaFrame.encode_length_pos message.solaFrame _ (encodeMany_length_ge SolaFrame.encode SolaFrame.encode_length_pos message.solaFrame), some_bind]
  rfl

end Packet

end Omi.TmxMxSolamulticastHsvfV1122
