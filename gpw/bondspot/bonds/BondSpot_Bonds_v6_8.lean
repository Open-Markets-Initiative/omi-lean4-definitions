import Wire

/-!
# Giełda Papierów Wartościowych w Warszawie BondSpot Bonds v6.8

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.GpwBondspotBondsXdpV68

/-- Message Indicator: one byte code -/
def MessageIndicator.codes : List UInt8 :=
  [0x46, 0x54, 0x4B, 0x53]

inductive MessageIndicator where
  | fixing -- Fixing
  | trade -- Trade
  | bidTheIndicativeBuyPriceOrTheBestBuyQuotePriceDependingOnTheFieldLevelOfTheMessage -- Bid The Indicative Buy Price Or The Best Buy Quote Price Depending On The Field Level Of The Message
  | askTheIndicativeSellPriceOrTheBestSellQuotePriceDependingOnTheFieldLevelOfTheMessage -- Ask The Indicative Sell Price Or The Best Sell Quote Price Depending On The Field Level Of The Message
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageIndicator

def toByte : MessageIndicator → UInt8
  | .fixing => 0x46
  | .trade => 0x54
  | .bidTheIndicativeBuyPriceOrTheBestBuyQuotePriceDependingOnTheFieldLevelOfTheMessage => 0x4B
  | .askTheIndicativeSellPriceOrTheBestSellQuotePriceDependingOnTheFieldLevelOfTheMessage => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageIndicator :=
  if byte = 0x46 then .fixing
  else if byte = 0x54 then .trade
  else if byte = 0x4B then .bidTheIndicativeBuyPriceOrTheBestBuyQuotePriceDependingOnTheFieldLevelOfTheMessage
  else .askTheIndicativeSellPriceOrTheBestSellQuotePriceDependingOnTheFieldLevelOfTheMessage

def ofByte (byte : UInt8) : MessageIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageIndicator) : ofByte value.toByte = value := by
  cases value with
  | fixing => decide
  | trade => decide
  | bidTheIndicativeBuyPriceOrTheBestBuyQuotePriceDependingOnTheFieldLevelOfTheMessage => decide
  | askTheIndicativeSellPriceOrTheBestSellQuotePriceDependingOnTheFieldLevelOfTheMessage => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MessageIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MessageIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageIndicator

/-- Algorithm Indicator: one byte code -/
def AlgorithmIndicator.codes : List UInt8 :=
  [0x31, 0x32]

inductive AlgorithmIndicator where
  | ismallpAlgorithm -- Ismallp Algorithm
  | ismaAlgorithm -- Isma Algorithm
  | unlisted (byte : { byte : UInt8 // byte ∉ AlgorithmIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AlgorithmIndicator

def toByte : AlgorithmIndicator → UInt8
  | .ismallpAlgorithm => 0x31
  | .ismaAlgorithm => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AlgorithmIndicator :=
  if byte = 0x31 then .ismallpAlgorithm
  else .ismaAlgorithm

def ofByte (byte : UInt8) : AlgorithmIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AlgorithmIndicator) : ofByte value.toByte = value := by
  cases value with
  | ismallpAlgorithm => decide
  | ismaAlgorithm => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AlgorithmIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AlgorithmIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AlgorithmIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AlgorithmIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AlgorithmIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AlgorithmIndicator

/-- Maturity Indicator: one byte code -/
def MaturityIndicator.codes : List UInt8 :=
  [0x30, 0x31]

inductive MaturityIndicator where
  | dateOfMaturityInAccordanceWithAProspect -- Date Of Maturity In Accordance With A Prospect
  | previouslyDateOfMaturity -- Previously Date Of Maturity
  | unlisted (byte : { byte : UInt8 // byte ∉ MaturityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MaturityIndicator

def toByte : MaturityIndicator → UInt8
  | .dateOfMaturityInAccordanceWithAProspect => 0x30
  | .previouslyDateOfMaturity => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MaturityIndicator :=
  if byte = 0x30 then .dateOfMaturityInAccordanceWithAProspect
  else .previouslyDateOfMaturity

def ofByte (byte : UInt8) : MaturityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MaturityIndicator) : ofByte value.toByte = value := by
  cases value with
  | dateOfMaturityInAccordanceWithAProspect => decide
  | previouslyDateOfMaturity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MaturityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MaturityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MaturityIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MaturityIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MaturityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MaturityIndicator

/-- Message Level: one byte code -/
def MessageLevel.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35]

inductive MessageLevel where
  | theFieldsPriceAndYtmCarryValuesDependingOnTheValueOfFieldMessageIndicator -- The Fields Price And Ytm Carry Values Depending On The Value Of Field Message Indicator
  | firstOfTheFiveBestBuyOrSellPriceLimits -- First Of The Five Best Buy Or Sell Price Limits
  | secondOfTheFiveBestBuyOrSellPriceLimits -- Second Of The Five Best Buy Or Sell Price Limits
  | thirdOfTheFiveBestBuyOrSellPriceLimits -- Third Of The Five Best Buy Or Sell Price Limits
  | fourthOfTheFiveBestBuyOrSellPriceLimits -- Fourth Of The Five Best Buy Or Sell Price Limits
  | fifthOfTheFiveBestBuyOrSellPriceLimits -- Fifth Of The Five Best Buy Or Sell Price Limits
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageLevel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageLevel

def toByte : MessageLevel → UInt8
  | .theFieldsPriceAndYtmCarryValuesDependingOnTheValueOfFieldMessageIndicator => 0x30
  | .firstOfTheFiveBestBuyOrSellPriceLimits => 0x31
  | .secondOfTheFiveBestBuyOrSellPriceLimits => 0x32
  | .thirdOfTheFiveBestBuyOrSellPriceLimits => 0x33
  | .fourthOfTheFiveBestBuyOrSellPriceLimits => 0x34
  | .fifthOfTheFiveBestBuyOrSellPriceLimits => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageLevel :=
  if byte = 0x30 then .theFieldsPriceAndYtmCarryValuesDependingOnTheValueOfFieldMessageIndicator
  else if byte = 0x31 then .firstOfTheFiveBestBuyOrSellPriceLimits
  else if byte = 0x32 then .secondOfTheFiveBestBuyOrSellPriceLimits
  else if byte = 0x33 then .thirdOfTheFiveBestBuyOrSellPriceLimits
  else if byte = 0x34 then .fourthOfTheFiveBestBuyOrSellPriceLimits
  else .fifthOfTheFiveBestBuyOrSellPriceLimits

def ofByte (byte : UInt8) : MessageLevel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageLevel) : ofByte value.toByte = value := by
  cases value with
  | theFieldsPriceAndYtmCarryValuesDependingOnTheValueOfFieldMessageIndicator => decide
  | firstOfTheFiveBestBuyOrSellPriceLimits => decide
  | secondOfTheFiveBestBuyOrSellPriceLimits => decide
  | thirdOfTheFiveBestBuyOrSellPriceLimits => decide
  | fourthOfTheFiveBestBuyOrSellPriceLimits => decide
  | fifthOfTheFiveBestBuyOrSellPriceLimits => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageLevel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageLevel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MessageLevel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MessageLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageLevel

/-- Accrued Interest Group: 8 bytes -/
structure AccruedInterestGroup where
  date : BitVec 32
  accruedInterest : BitVec 32
  deriving DecidableEq, Repr

namespace AccruedInterestGroup

def encode (message : AccruedInterestGroup) : List UInt8 :=
  encodeUInt 4 message.date
    ++ (encodeUInt 4 message.accruedInterest)

def decode (bytes : List UInt8) : Option (AccruedInterestGroup × List UInt8) := do
  let (date, bytes) ← decodeUInt 4 bytes
  let (accruedInterest, bytes) ← decodeUInt 4 bytes
  pure ({ date, accruedInterest }, bytes)

@[simp] theorem encode_length (message : AccruedInterestGroup) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AccruedInterestGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccruedInterestGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AccruedInterestGroup

/-- Accrued Interest Message: 272 bytes -/
structure AccruedInterestMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  numberDays : BitVec 16
  sourceTimeMicroSecs : BitVec 16
  accruedInterestScaleCode : BitVec 8
  reserved3 : Alpha 3
  accruedInterestGroup : Exact 31 AccruedInterestGroup
  deriving DecidableEq, Repr

namespace AccruedInterestMessage

def encode (message : AccruedInterestMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 2 message.numberDays
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.accruedInterestScaleCode
    ++ (Alpha.encode message.reserved3
    ++ (encodeMany AccruedInterestGroup.encode message.accruedInterestGroup.val))))))))

def decode (bytes : List UInt8) : Option (AccruedInterestMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (numberDays, bytes) ← decodeUInt 2 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (accruedInterestScaleCode, bytes) ← decodeUInt 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  let (accruedInterestGroup_, bytes) ← decodeMany AccruedInterestGroup.decode 31 bytes
  if fits_accruedInterestGroup : accruedInterestGroup_.length = 31 then
    pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, numberDays, sourceTimeMicroSecs, accruedInterestScaleCode, reserved3, accruedInterestGroup := ⟨accruedInterestGroup_, fits_accruedInterestGroup⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : AccruedInterestMessage) : (encode message).length = 272 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeMany_length_const AccruedInterestGroup.encode 8 AccruedInterestGroup.encode_length, message.accruedInterestGroup.length_eq]

theorem encode_length_pos (message : AccruedInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccruedInterestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_exact 31 AccruedInterestGroup.encode AccruedInterestGroup.decode AccruedInterestGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.accruedInterestGroup.length_eq]
  rfl

end AccruedInterestMessage

/-- Interest For Settlement Day Message: 40 bytes -/
structure InterestForSettlementDayMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  date : BitVec 32
  settlementDate : Alpha 8
  interest : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  currency : Alpha 3
  interestScaleCode : BitVec 8
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace InterestForSettlementDayMessage

def encode (message : InterestForSettlementDayMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.date
    ++ (Alpha.encode message.settlementDate
    ++ (encodeUInt 4 message.interest
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 1 message.interestScaleCode
    ++ (Alpha.encode message.reserved2))))))))))

def decode (bytes : List UInt8) : Option (InterestForSettlementDayMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 4 bytes
  let (settlementDate, bytes) ← Alpha.decode 8 bytes
  let (interest, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (interestScaleCode, bytes) ← decodeUInt 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, date, settlementDate, interest, sourceTimeMicroSecs, currency, interestScaleCode, reserved2 }, bytes)

@[simp] theorem encode_length (message : InterestForSettlementDayMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InterestForSettlementDayMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InterestForSettlementDayMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InterestForSettlementDayMessage

/-- Yield To Maturity Message: 44 bytes -/
structure YieldToMaturityMessage where
  symbolIndex : BitVec 32
  sourceTime : BitVec 32
  sourceSeqNum : BitVec 32
  systemId : BitVec 32
  date : BitVec 32
  price : BitVec 32
  sourceTimeMicroSecs : BitVec 16
  ytmScaleCode : BitVec 8
  priceScaleCode : BitVec 8
  ytm : BitVec 32
  messageIndicator : MessageIndicator
  algorithmIndicator : AlgorithmIndicator
  maturityIndicator : MaturityIndicator
  messageLevel : MessageLevel
  maturityDate : BitVec 32
  tradeIdNumber : BitVec 32
  deriving DecidableEq, Repr

namespace YieldToMaturityMessage

def encode (message : YieldToMaturityMessage) : List UInt8 :=
  encodeUInt 4 message.symbolIndex
    ++ (encodeUInt 4 message.sourceTime
    ++ (encodeUInt 4 message.sourceSeqNum
    ++ (encodeUInt 4 message.systemId
    ++ (encodeUInt 4 message.date
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.sourceTimeMicroSecs
    ++ (encodeUInt 1 message.ytmScaleCode
    ++ (encodeUInt 1 message.priceScaleCode
    ++ (encodeUInt 4 message.ytm
    ++ (MessageIndicator.encode message.messageIndicator
    ++ (AlgorithmIndicator.encode message.algorithmIndicator
    ++ (MaturityIndicator.encode message.maturityIndicator
    ++ (MessageLevel.encode message.messageLevel
    ++ (encodeUInt 4 message.maturityDate
    ++ (encodeUInt 4 message.tradeIdNumber)))))))))))))))

def decode (bytes : List UInt8) : Option (YieldToMaturityMessage × List UInt8) := do
  let (symbolIndex, bytes) ← decodeUInt 4 bytes
  let (sourceTime, bytes) ← decodeUInt 4 bytes
  let (sourceSeqNum, bytes) ← decodeUInt 4 bytes
  let (systemId, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (sourceTimeMicroSecs, bytes) ← decodeUInt 2 bytes
  let (ytmScaleCode, bytes) ← decodeUInt 1 bytes
  let (priceScaleCode, bytes) ← decodeUInt 1 bytes
  let (ytm, bytes) ← decodeUInt 4 bytes
  let (messageIndicator, bytes) ← MessageIndicator.decode bytes
  let (algorithmIndicator, bytes) ← AlgorithmIndicator.decode bytes
  let (maturityIndicator, bytes) ← MaturityIndicator.decode bytes
  let (messageLevel, bytes) ← MessageLevel.decode bytes
  let (maturityDate, bytes) ← decodeUInt 4 bytes
  let (tradeIdNumber, bytes) ← decodeUInt 4 bytes
  pure ({ symbolIndex, sourceTime, sourceSeqNum, systemId, date, price, sourceTimeMicroSecs, ytmScaleCode, priceScaleCode, ytm, messageIndicator, algorithmIndicator, maturityIndicator, messageLevel, maturityDate, tradeIdNumber }, bytes)

@[simp] theorem encode_length (message : YieldToMaturityMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MessageIndicator.encode_length, AlgorithmIndicator.encode_length, MaturityIndicator.encode_length, MessageLevel.encode_length]

theorem encode_length_pos (message : YieldToMaturityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : YieldToMaturityMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MessageIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgorithmIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MaturityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MessageLevel.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end YieldToMaturityMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | accruedInterestMessage (message : AccruedInterestMessage) -- 601
  | interestForSettlementDayMessage (message : InterestForSettlementDayMessage) -- 602
  | yieldToMaturityMessage (message : YieldToMaturityMessage) -- 603
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 16
  | .accruedInterestMessage _ => 601
  | .interestForSettlementDayMessage _ => 602
  | .yieldToMaturityMessage _ => 603

def encode : Payload → List UInt8
  | .accruedInterestMessage message => AccruedInterestMessage.encode message
  | .interestForSettlementDayMessage message => InterestForSettlementDayMessage.encode message
  | .yieldToMaturityMessage message => YieldToMaturityMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 272 := by
  cases message with
  | accruedInterestMessage inner =>
    simp only [encode, AccruedInterestMessage.encode_length]
    omega
  | interestForSettlementDayMessage inner =>
    simp only [encode, InterestForSettlementDayMessage.encode_length]
    omega
  | yieldToMaturityMessage inner =>
    simp only [encode, YieldToMaturityMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 601 then (AccruedInterestMessage.decode bytes).map fun (message, rest) => (.accruedInterestMessage message, rest)
  else if tag = 602 then (InterestForSettlementDayMessage.decode bytes).map fun (message, rest) => (.interestForSettlementDayMessage message, rest)
  else if tag = 603 then (YieldToMaturityMessage.decode bytes).map fun (message, rest) => (.yieldToMaturityMessage message, rest)
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
  | accruedInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AccruedInterestMessage.encode_length]
    omega
  | interestForSettlementDayMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InterestForSettlementDayMessage.encode_length]
    omega
  | yieldToMaturityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, YieldToMaturityMessage.encode_length]
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

end Omi.GpwBondspotBondsXdpV68
