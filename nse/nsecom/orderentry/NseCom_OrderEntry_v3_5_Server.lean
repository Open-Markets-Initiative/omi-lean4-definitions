import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v3.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NseNsecomOrderentryNnfV35Server

/-- St Market Status: 8 bytes -/
structure StMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StMarketStatus

def encode (message : StMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StMarketStatus) (rest : List UInt8) :
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

end StMarketStatus

/-- St Ex Market Status: 8 bytes -/
structure StExMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StExMarketStatus

def encode (message : StExMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StExMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StExMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StExMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StExMarketStatus) (rest : List UInt8) :
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

end StExMarketStatus

/-- St Pl Market Status: 8 bytes -/
structure StPlMarketStatus where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  deriving DecidableEq, Repr

namespace StPlMarketStatus

def encode (message : StPlMarketStatus) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction)))

def decode (bytes : List UInt8) : Option (StPlMarketStatus × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  pure ({ normal, oddlot, spot, auction }, bytes)

@[simp] theorem encode_length (message : StPlMarketStatus) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StPlMarketStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StPlMarketStatus) (rest : List UInt8) :
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

end StPlMarketStatus

/-- System Information Out Message: 66 bytes -/
structure SystemInformationOutMessage where
  stMarketStatus : StMarketStatus
  stExMarketStatus : StExMarketStatus
  stPlMarketStatus : StPlMarketStatus
  updatePortfolio : Alpha 1
  cFiller : Alpha 1
  marketIndex : BitVec 32
  defaultSettlementPeriodNormal : BitVec 16
  defaultSettlementPeriodSpot : BitVec 16
  defaultSettlementPeriodAuction : BitVec 16
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  warningPercent : BitVec 16
  volumeFreezePercent : BitVec 16
  snapQuoteTime : BitVec 16
  reserved2 : Alpha 2
  boardLotQuantity : BitVec 32
  tickSize : BitVec 32
  maximumGtcDays : BitVec 16
  stStockEligibleIndicators : BitVec 16
  disclosedQuantityPercentAllowed : BitVec 16
  riskFreeInterestRate : BitVec 32
  deriving DecidableEq, Repr

namespace SystemInformationOutMessage

def encode (message : SystemInformationOutMessage) : List UInt8 :=
  StMarketStatus.encode message.stMarketStatus
    ++ (StExMarketStatus.encode message.stExMarketStatus
    ++ (StPlMarketStatus.encode message.stPlMarketStatus
    ++ (Alpha.encode message.updatePortfolio
    ++ (Alpha.encode message.cFiller
    ++ (encodeUInt 4 message.marketIndex
    ++ (encodeUInt 2 message.defaultSettlementPeriodNormal
    ++ (encodeUInt 2 message.defaultSettlementPeriodSpot
    ++ (encodeUInt 2 message.defaultSettlementPeriodAuction
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.warningPercent
    ++ (encodeUInt 2 message.volumeFreezePercent
    ++ (encodeUInt 2 message.snapQuoteTime
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 4 message.boardLotQuantity
    ++ (encodeUInt 4 message.tickSize
    ++ (encodeUInt 2 message.maximumGtcDays
    ++ (encodeUInt 2 message.stStockEligibleIndicators
    ++ (encodeUInt 2 message.disclosedQuantityPercentAllowed
    ++ (encodeUInt 4 message.riskFreeInterestRate))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SystemInformationOutMessage × List UInt8) := do
  let (stMarketStatus, bytes) ← StMarketStatus.decode bytes
  let (stExMarketStatus, bytes) ← StExMarketStatus.decode bytes
  let (stPlMarketStatus, bytes) ← StPlMarketStatus.decode bytes
  let (updatePortfolio, bytes) ← Alpha.decode 1 bytes
  let (cFiller, bytes) ← Alpha.decode 1 bytes
  let (marketIndex, bytes) ← decodeUInt 4 bytes
  let (defaultSettlementPeriodNormal, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodSpot, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodAuction, bytes) ← decodeUInt 2 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (warningPercent, bytes) ← decodeUInt 2 bytes
  let (volumeFreezePercent, bytes) ← decodeUInt 2 bytes
  let (snapQuoteTime, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (boardLotQuantity, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 4 bytes
  let (maximumGtcDays, bytes) ← decodeUInt 2 bytes
  let (stStockEligibleIndicators, bytes) ← decodeUInt 2 bytes
  let (disclosedQuantityPercentAllowed, bytes) ← decodeUInt 2 bytes
  let (riskFreeInterestRate, bytes) ← decodeUInt 4 bytes
  pure ({ stMarketStatus, stExMarketStatus, stPlMarketStatus, updatePortfolio, cFiller, marketIndex, defaultSettlementPeriodNormal, defaultSettlementPeriodSpot, defaultSettlementPeriodAuction, competitorPeriod, solicitorPeriod, warningPercent, volumeFreezePercent, snapQuoteTime, reserved2, boardLotQuantity, tickSize, maximumGtcDays, stStockEligibleIndicators, disclosedQuantityPercentAllowed, riskFreeInterestRate }, bytes)

@[simp] theorem encode_length (message : SystemInformationOutMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, StMarketStatus.encode_length, StExMarketStatus.encode_length, StPlMarketStatus.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SystemInformationOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemInformationOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StExMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StPlMarketStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemInformationOutMessage

/-- Partial System Information Message: 66 bytes -/
structure PartialSystemInformationMessage where
  stMarketStatus : StMarketStatus
  stExMarketStatus : StExMarketStatus
  stPlMarketStatus : StPlMarketStatus
  updatePortfolio : Alpha 1
  cFiller : Alpha 1
  marketIndex : BitVec 32
  defaultSettlementPeriodNormal : BitVec 16
  defaultSettlementPeriodSpot : BitVec 16
  defaultSettlementPeriodAuction : BitVec 16
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  warningPercent : BitVec 16
  volumeFreezePercent : BitVec 16
  snapQuoteTime : BitVec 16
  reserved2 : Alpha 2
  boardLotQuantity : BitVec 32
  tickSize : BitVec 32
  maximumGtcDays : BitVec 16
  stStockEligibleIndicators : BitVec 16
  disclosedQuantityPercentAllowed : BitVec 16
  riskFreeInterestRate : BitVec 32
  deriving DecidableEq, Repr

namespace PartialSystemInformationMessage

def encode (message : PartialSystemInformationMessage) : List UInt8 :=
  StMarketStatus.encode message.stMarketStatus
    ++ (StExMarketStatus.encode message.stExMarketStatus
    ++ (StPlMarketStatus.encode message.stPlMarketStatus
    ++ (Alpha.encode message.updatePortfolio
    ++ (Alpha.encode message.cFiller
    ++ (encodeUInt 4 message.marketIndex
    ++ (encodeUInt 2 message.defaultSettlementPeriodNormal
    ++ (encodeUInt 2 message.defaultSettlementPeriodSpot
    ++ (encodeUInt 2 message.defaultSettlementPeriodAuction
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.warningPercent
    ++ (encodeUInt 2 message.volumeFreezePercent
    ++ (encodeUInt 2 message.snapQuoteTime
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 4 message.boardLotQuantity
    ++ (encodeUInt 4 message.tickSize
    ++ (encodeUInt 2 message.maximumGtcDays
    ++ (encodeUInt 2 message.stStockEligibleIndicators
    ++ (encodeUInt 2 message.disclosedQuantityPercentAllowed
    ++ (encodeUInt 4 message.riskFreeInterestRate))))))))))))))))))))

def decode (bytes : List UInt8) : Option (PartialSystemInformationMessage × List UInt8) := do
  let (stMarketStatus, bytes) ← StMarketStatus.decode bytes
  let (stExMarketStatus, bytes) ← StExMarketStatus.decode bytes
  let (stPlMarketStatus, bytes) ← StPlMarketStatus.decode bytes
  let (updatePortfolio, bytes) ← Alpha.decode 1 bytes
  let (cFiller, bytes) ← Alpha.decode 1 bytes
  let (marketIndex, bytes) ← decodeUInt 4 bytes
  let (defaultSettlementPeriodNormal, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodSpot, bytes) ← decodeUInt 2 bytes
  let (defaultSettlementPeriodAuction, bytes) ← decodeUInt 2 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (warningPercent, bytes) ← decodeUInt 2 bytes
  let (volumeFreezePercent, bytes) ← decodeUInt 2 bytes
  let (snapQuoteTime, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (boardLotQuantity, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 4 bytes
  let (maximumGtcDays, bytes) ← decodeUInt 2 bytes
  let (stStockEligibleIndicators, bytes) ← decodeUInt 2 bytes
  let (disclosedQuantityPercentAllowed, bytes) ← decodeUInt 2 bytes
  let (riskFreeInterestRate, bytes) ← decodeUInt 4 bytes
  pure ({ stMarketStatus, stExMarketStatus, stPlMarketStatus, updatePortfolio, cFiller, marketIndex, defaultSettlementPeriodNormal, defaultSettlementPeriodSpot, defaultSettlementPeriodAuction, competitorPeriod, solicitorPeriod, warningPercent, volumeFreezePercent, snapQuoteTime, reserved2, boardLotQuantity, tickSize, maximumGtcDays, stStockEligibleIndicators, disclosedQuantityPercentAllowed, riskFreeInterestRate }, bytes)

@[simp] theorem encode_length (message : PartialSystemInformationMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, StMarketStatus.encode_length, StExMarketStatus.encode_length, StPlMarketStatus.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PartialSystemInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialSystemInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StExMarketStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StPlMarketStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartialSystemInformationMessage

/-- Open Order Report Message: 68 bytes -/
structure OpenOrderReportMessage where
  messageType : Alpha 1
  reportDate : BitVec 32
  userType : BitVec 16
  brokerId : Alpha 5
  firmName : Alpha 25
  traderNumber : BitVec 32
  traderName : Alpha 26
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace OpenOrderReportMessage

def encode (message : OpenOrderReportMessage) : List UInt8 :=
  Alpha.encode message.messageType
    ++ (encodeUInt 4 message.reportDate
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.firmName
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.traderName
    ++ (Alpha.encode message.reserved1)))))))

def decode (bytes : List UInt8) : Option (OpenOrderReportMessage × List UInt8) := do
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (reportDate, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (firmName, bytes) ← Alpha.decode 25 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ messageType, reportDate, userType, brokerId, firmName, traderNumber, traderName, reserved1 }, bytes)

@[simp] theorem encode_length (message : OpenOrderReportMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OpenOrderReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenOrderReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OpenOrderReportMessage

/-- Spread Order Log Report Message: 68 bytes -/
structure SpreadOrderLogReportMessage where
  messageType : Alpha 1
  reportDate : BitVec 32
  userType : BitVec 16
  brokerId : Alpha 5
  firmName : Alpha 25
  traderNumber : BitVec 32
  traderName : Alpha 26
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SpreadOrderLogReportMessage

def encode (message : SpreadOrderLogReportMessage) : List UInt8 :=
  Alpha.encode message.messageType
    ++ (encodeUInt 4 message.reportDate
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.firmName
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.traderName
    ++ (Alpha.encode message.reserved1)))))))

def decode (bytes : List UInt8) : Option (SpreadOrderLogReportMessage × List UInt8) := do
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (reportDate, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (firmName, bytes) ← Alpha.decode 25 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ messageType, reportDate, userType, brokerId, firmName, traderNumber, traderName, reserved1 }, bytes)

@[simp] theorem encode_length (message : SpreadOrderLogReportMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadOrderLogReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderLogReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpreadOrderLogReportMessage

/-- Spread Trade Report Message: 68 bytes -/
structure SpreadTradeReportMessage where
  messageType : Alpha 1
  reportDate : BitVec 32
  userType : BitVec 16
  brokerId : Alpha 5
  firmName : Alpha 25
  traderNumber : BitVec 32
  traderName : Alpha 26
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SpreadTradeReportMessage

def encode (message : SpreadTradeReportMessage) : List UInt8 :=
  Alpha.encode message.messageType
    ++ (encodeUInt 4 message.reportDate
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.firmName
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.traderName
    ++ (Alpha.encode message.reserved1)))))))

def decode (bytes : List UInt8) : Option (SpreadTradeReportMessage × List UInt8) := do
  let (messageType, bytes) ← Alpha.decode 1 bytes
  let (reportDate, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (firmName, bytes) ← Alpha.decode 25 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ messageType, reportDate, userType, brokerId, firmName, traderNumber, traderName, reserved1 }, bytes)

@[simp] theorem encode_length (message : SpreadTradeReportMessage) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadTradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadTradeReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpreadTradeReportMessage

/-- Contract Desc: 28 bytes -/
structure ContractDesc where
  instrumentName : Alpha 6
  symbol : Alpha 10
  expiryDate : BitVec 32
  strikePrice : BitVec 32
  optionType : Alpha 2
  caLevel : BitVec 16
  deriving DecidableEq, Repr

namespace ContractDesc

def encode (message : ContractDesc) : List UInt8 :=
  Alpha.encode message.instrumentName
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.strikePrice
    ++ (Alpha.encode message.optionType
    ++ (encodeUInt 2 message.caLevel)))))

def decode (bytes : List UInt8) : Option (ContractDesc × List UInt8) := do
  let (instrumentName, bytes) ← Alpha.decode 6 bytes
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 2 bytes
  let (caLevel, bytes) ← decodeUInt 2 bytes
  pure ({ instrumentName, symbol, expiryDate, strikePrice, optionType, caLevel }, bytes)

@[simp] theorem encode_length (message : ContractDesc) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ContractDesc) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContractDesc) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContractDesc

/-- Board Lot Out Message: 276 bytes -/
structure BoardLotOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace BoardLotOutMessage

def encode (message : BoardLotOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BoardLotOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : BoardLotOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BoardLotOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BoardLotOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoardLotOutMessage

/-- Neg Order To Bl Message: 276 bytes -/
structure NegOrderToBlMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace NegOrderToBlMessage

def encode (message : NegOrderToBlMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NegOrderToBlMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : NegOrderToBlMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NegOrderToBlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NegOrderToBlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NegOrderToBlMessage

/-- Order Mod Out Message: 276 bytes -/
structure OrderModOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModOutMessage

def encode (message : OrderModOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModOutMessage

/-- Order Mod Reject Message: 276 bytes -/
structure OrderModRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModRejectMessage

def encode (message : OrderModRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModRejectMessage

/-- Order Cancel Out Message: 276 bytes -/
structure OrderCancelOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelOutMessage

def encode (message : OrderCancelOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelOutMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelOutMessage

/-- Order Cancel Reject Message: 276 bytes -/
structure OrderCancelRejectMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Order Confirmation Message: 276 bytes -/
structure OrderConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderConfirmationMessage

def encode (message : OrderConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderConfirmationMessage

/-- Order Mod Confirmation Message: 276 bytes -/
structure OrderModConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderModConfirmationMessage

def encode (message : OrderModConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderModConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderModConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderModConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModConfirmationMessage

/-- Order Cancel Confirmation Message: 276 bytes -/
structure OrderCancelConfirmationMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderCancelConfirmationMessage

def encode (message : OrderCancelConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelConfirmationMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderCancelConfirmationMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderCancelConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelConfirmationMessage

/-- Cancel Neg Order Message: 276 bytes -/
structure CancelNegOrderMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace CancelNegOrderMessage

def encode (message : CancelNegOrderMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (CancelNegOrderMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : CancelNegOrderMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CancelNegOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : CancelNegOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelNegOrderMessage

/-- Freeze To Control Message: 276 bytes -/
structure FreezeToControlMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace FreezeToControlMessage

def encode (message : FreezeToControlMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FreezeToControlMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : FreezeToControlMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : FreezeToControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FreezeToControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FreezeToControlMessage

/-- Order Error Message: 276 bytes -/
structure OrderErrorMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderErrorMessage

def encode (message : OrderErrorMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderErrorMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderErrorMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderErrorMessage

/-- Batch Order Cancel Message: 276 bytes -/
structure BatchOrderCancelMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modifiedCancelledBy : Alpha 1
  secondReserved1 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  counterPartyBrokerId : Alpha 5
  thirdReserved1 : Alpha 1
  reserved2 : Alpha 2
  closeoutFlag : Alpha 1
  fourthReserved1 : Alpha 1
  orderType : BitVec 16
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookTypeShort2 : BitVec 16
  buySellIndicator : BitVec 16
  disclosedVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  totalVolumeRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minimumFillAonVolume : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  cOrdFiller : Alpha 24
  openClose : Alpha 1
  settlor : Alpha 12
  proClientIndicator : BitVec 16
  settlementPeriod : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag : Alpha 1
  reference : Alpha 4
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace BatchOrderCancelMessage

def encode (message : BatchOrderCancelMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modifiedCancelledBy
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.counterPartyBrokerId
    ++ (Alpha.encode message.thirdReserved1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.closeoutFlag
    ++ (Alpha.encode message.fourthReserved1
    ++ (encodeUInt 2 message.orderType
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookTypeShort2
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.totalVolumeRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minimumFillAonVolume
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClientIndicator
    ++ (encodeUInt 2 message.settlementPeriod
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag
    ++ (Alpha.encode message.reference
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BatchOrderCancelMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modifiedCancelledBy, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (counterPartyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (closeoutFlag, bytes) ← Alpha.decode 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← decodeUInt 2 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookTypeShort2, bytes) ← decodeUInt 2 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minimumFillAonVolume, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClientIndicator, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag, bytes) ← Alpha.decode 1 bytes
  let (reference, bytes) ← Alpha.decode 4 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modifiedCancelledBy, secondReserved1, reasonCode, reserved4, tokenNo, contractDesc, counterPartyBrokerId, thirdReserved1, reserved2, closeoutFlag, fourthReserved1, orderType, orderNumber, accountNumber, bookTypeShort2, buySellIndicator, disclosedVolume, disclosedVolumeRemaining, totalVolumeRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minimumFillAonVolume, lastModified, stOrderFlags, branchId, traderId, brokerId, cOrdFiller, openClose, settlor, proClientIndicator, settlementPeriod, additionalOrderFlags, giveupFlag, reference, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : BatchOrderCancelMessage) : (encode message).length = 276 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BatchOrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BatchOrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BatchOrderCancelMessage

/-- Ms Spd Leg Info Leg 2: 80 bytes -/
structure MsSpdLegInfoLeg2 where
  token2 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId2 : Alpha 5
  fillerx2 : Alpha 1
  orderType2 : BitVec 16
  buySell2 : BitVec 16
  disclosedVol2 : BitVec 32
  disclosedVolRemaining2 : BitVec 32
  totalVolRemaining2 : BitVec 32
  volume2 : BitVec 32
  volumeFilledToday2 : BitVec 32
  price2 : BitVec 32
  triggerPrice2 : BitVec 32
  minFillAon2 : BitVec 32
  stOrderFlags : BitVec 16
  openClose2 : Alpha 1
  additionalOrderFlags : BitVec 8
  giveupFlag2 : Alpha 1
  fillerY : Alpha 1
  deriving DecidableEq, Repr

namespace MsSpdLegInfoLeg2

def encode (message : MsSpdLegInfoLeg2) : List UInt8 :=
  encodeUInt 4 message.token2
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId2
    ++ (Alpha.encode message.fillerx2
    ++ (encodeUInt 2 message.orderType2
    ++ (encodeUInt 2 message.buySell2
    ++ (encodeUInt 4 message.disclosedVol2
    ++ (encodeUInt 4 message.disclosedVolRemaining2
    ++ (encodeUInt 4 message.totalVolRemaining2
    ++ (encodeUInt 4 message.volume2
    ++ (encodeUInt 4 message.volumeFilledToday2
    ++ (encodeUInt 4 message.price2
    ++ (encodeUInt 4 message.triggerPrice2
    ++ (encodeUInt 4 message.minFillAon2
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (Alpha.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag2
    ++ (Alpha.encode message.fillerY))))))))))))))))))

def decode (bytes : List UInt8) : Option (MsSpdLegInfoLeg2 × List UInt8) := do
  let (token2, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId2, bytes) ← Alpha.decode 5 bytes
  let (fillerx2, bytes) ← Alpha.decode 1 bytes
  let (orderType2, bytes) ← decodeUInt 2 bytes
  let (buySell2, bytes) ← decodeUInt 2 bytes
  let (disclosedVol2, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (volume2, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday2, bytes) ← decodeUInt 4 bytes
  let (price2, bytes) ← decodeUInt 4 bytes
  let (triggerPrice2, bytes) ← decodeUInt 4 bytes
  let (minFillAon2, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (openClose2, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag2, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, giveupFlag2, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg2) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MsSpdLegInfoLeg2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsSpdLegInfoLeg2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfoLeg2

/-- Ms Spd Leg Info Leg 3: 80 bytes -/
structure MsSpdLegInfoLeg3 where
  token2 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId2 : Alpha 5
  fillerx2 : Alpha 1
  orderType2 : BitVec 16
  buySell2 : BitVec 16
  disclosedVol2 : BitVec 32
  disclosedVolRemaining2 : BitVec 32
  totalVolRemaining2 : BitVec 32
  volume2 : BitVec 32
  volumeFilledToday2 : BitVec 32
  price2 : BitVec 32
  triggerPrice2 : BitVec 32
  minFillAon2 : BitVec 32
  stOrderFlags : BitVec 16
  openClose2 : Alpha 1
  additionalOrderFlags : BitVec 8
  giveupFlag2 : Alpha 1
  fillerY : Alpha 1
  deriving DecidableEq, Repr

namespace MsSpdLegInfoLeg3

def encode (message : MsSpdLegInfoLeg3) : List UInt8 :=
  encodeUInt 4 message.token2
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId2
    ++ (Alpha.encode message.fillerx2
    ++ (encodeUInt 2 message.orderType2
    ++ (encodeUInt 2 message.buySell2
    ++ (encodeUInt 4 message.disclosedVol2
    ++ (encodeUInt 4 message.disclosedVolRemaining2
    ++ (encodeUInt 4 message.totalVolRemaining2
    ++ (encodeUInt 4 message.volume2
    ++ (encodeUInt 4 message.volumeFilledToday2
    ++ (encodeUInt 4 message.price2
    ++ (encodeUInt 4 message.triggerPrice2
    ++ (encodeUInt 4 message.minFillAon2
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (Alpha.encode message.openClose2
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag2
    ++ (Alpha.encode message.fillerY))))))))))))))))))

def decode (bytes : List UInt8) : Option (MsSpdLegInfoLeg3 × List UInt8) := do
  let (token2, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId2, bytes) ← Alpha.decode 5 bytes
  let (fillerx2, bytes) ← Alpha.decode 1 bytes
  let (orderType2, bytes) ← decodeUInt 2 bytes
  let (buySell2, bytes) ← decodeUInt 2 bytes
  let (disclosedVol2, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining2, bytes) ← decodeUInt 4 bytes
  let (volume2, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday2, bytes) ← decodeUInt 4 bytes
  let (price2, bytes) ← decodeUInt 4 bytes
  let (triggerPrice2, bytes) ← decodeUInt 4 bytes
  let (minFillAon2, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (openClose2, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag2, bytes) ← Alpha.decode 1 bytes
  let (fillerY, bytes) ← Alpha.decode 1 bytes
  pure ({ token2, contractDesc, opBrokerId2, fillerx2, orderType2, buySell2, disclosedVol2, disclosedVolRemaining2, totalVolRemaining2, volume2, volumeFilledToday2, price2, triggerPrice2, minFillAon2, stOrderFlags, openClose2, additionalOrderFlags, giveupFlag2, fillerY }, bytes)

@[simp] theorem encode_length (message : MsSpdLegInfoLeg3) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MsSpdLegInfoLeg3) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MsSpdLegInfoLeg3) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MsSpdLegInfoLeg3

/-- Sp Board Lot Out Message: 440 bytes -/
structure SpBoardLotOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpBoardLotOutMessage

def encode (message : SpBoardLotOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpBoardLotOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpBoardLotOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpBoardLotOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpBoardLotOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpBoardLotOutMessage

/-- Twol Board Lot Out Message: 440 bytes -/
structure TwolBoardLotOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolBoardLotOutMessage

def encode (message : TwolBoardLotOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolBoardLotOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolBoardLotOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolBoardLotOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolBoardLotOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolBoardLotOutMessage

/-- Thrl Board Lot Out Message: 440 bytes -/
structure ThrlBoardLotOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlBoardLotOutMessage

def encode (message : ThrlBoardLotOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlBoardLotOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlBoardLotOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlBoardLotOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlBoardLotOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlBoardLotOutMessage

/-- Sp Order Cancel Out Message: 440 bytes -/
structure SpOrderCancelOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderCancelOutMessage

def encode (message : SpOrderCancelOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderCancelOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderCancelOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderCancelOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderCancelOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderCancelOutMessage

/-- Sp Order Mod Out Message: 440 bytes -/
structure SpOrderModOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderModOutMessage

def encode (message : SpOrderModOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderModOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderModOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderModOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderModOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderModOutMessage

/-- Sp Order Confirmation Message: 440 bytes -/
structure SpOrderConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderConfirmationMessage

def encode (message : SpOrderConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderConfirmationMessage

/-- Twol Order Confirmation Message: 440 bytes -/
structure TwolOrderConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderConfirmationMessage

def encode (message : TwolOrderConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderConfirmationMessage

/-- Thrl Order Confirmation Message: 440 bytes -/
structure ThrlOrderConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderConfirmationMessage

def encode (message : ThrlOrderConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderConfirmationMessage

/-- Sp Order Cxl Rej Out Message: 440 bytes -/
structure SpOrderCxlRejOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderCxlRejOutMessage

def encode (message : SpOrderCxlRejOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderCxlRejOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderCxlRejOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderCxlRejOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderCxlRejOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderCxlRejOutMessage

/-- Sp Order Cxl Confirmation Message: 440 bytes -/
structure SpOrderCxlConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderCxlConfirmationMessage

def encode (message : SpOrderCxlConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderCxlConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderCxlConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderCxlConfirmationMessage

/-- Twol Order Cxl Confirmation Message: 440 bytes -/
structure TwolOrderCxlConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderCxlConfirmationMessage

def encode (message : TwolOrderCxlConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderCxlConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderCxlConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderCxlConfirmationMessage

/-- Thrl Order Cxl Confirmation Message: 440 bytes -/
structure ThrlOrderCxlConfirmationMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderCxlConfirmationMessage

def encode (message : ThrlOrderCxlConfirmationMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderCxlConfirmationMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderCxlConfirmationMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderCxlConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderCxlConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderCxlConfirmationMessage

/-- Sp Order Mod Rej Out Message: 440 bytes -/
structure SpOrderModRejOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderModRejOutMessage

def encode (message : SpOrderModRejOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderModRejOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderModRejOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderModRejOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderModRejOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderModRejOutMessage

/-- Sp Order Mod Con Out Message: 440 bytes -/
structure SpOrderModConOutMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace SpOrderModConOutMessage

def encode (message : SpOrderModConOutMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpOrderModConOutMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : SpOrderModConOutMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : SpOrderModConOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpOrderModConOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end SpOrderModConOutMessage

/-- Twol Order Error Message: 440 bytes -/
structure TwolOrderErrorMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace TwolOrderErrorMessage

def encode (message : TwolOrderErrorMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TwolOrderErrorMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : TwolOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : TwolOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TwolOrderErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end TwolOrderErrorMessage

/-- Thrl Order Error Message: 440 bytes -/
structure ThrlOrderErrorMessage where
  participantType1 : Alpha 1
  filler1 : Alpha 1
  competitorPeriod1 : BitVec 16
  solicitorPeriod1 : BitVec 16
  modCxlBy1 : Alpha 1
  filler9 : Alpha 1
  reasonCode1 : BitVec 16
  startAlpha1 : Alpha 2
  endAlpha1 : Alpha 2
  token1 : BitVec 32
  contractDesc : ContractDesc
  opBrokerId1 : Alpha 5
  fillerx1 : Alpha 1
  fillerOptions1 : Alpha 3
  fillery1 : Alpha 1
  orderType1 : BitVec 16
  orderNumber1 : Alpha 8
  accountNumber1 : Alpha 10
  bookType1 : BitVec 16
  buySell1 : BitVec 16
  disclosedVol1 : BitVec 32
  disclosedVolRemaining1 : BitVec 32
  totalVolRemaining1 : BitVec 32
  volume1 : BitVec 32
  volumeFilledToday1 : BitVec 32
  price1 : BitVec 32
  triggerPrice1 : BitVec 32
  goodTillDate1 : BitVec 32
  entryDateTime1 : BitVec 32
  minFillAon1 : BitVec 32
  lastModified1 : BitVec 32
  stOrderFlags : BitVec 16
  branchId1 : BitVec 16
  traderId1 : BitVec 32
  brokerId1 : Alpha 5
  cOrdFiller : Alpha 24
  openClose1 : Alpha 1
  settlor1 : Alpha 12
  proClient1 : BitVec 16
  settlementPeriod1 : BitVec 16
  additionalOrderFlags : BitVec 8
  giveupFlag1 : Alpha 1
  reserved2 : Alpha 2
  filler17 : Alpha 1
  filler18 : Alpha 1
  nnfField : Alpha 8
  mktReplay : Alpha 8
  pan : Alpha 10
  algoId : BitVec 32
  secondReserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  priceDiff : BitVec 32
  msSpdLegInfoLeg2 : MsSpdLegInfoLeg2
  msSpdLegInfoLeg3 : MsSpdLegInfoLeg3
  deriving DecidableEq, Repr

namespace ThrlOrderErrorMessage

def encode (message : ThrlOrderErrorMessage) : List UInt8 :=
  Alpha.encode message.participantType1
    ++ (Alpha.encode message.filler1
    ++ (encodeUInt 2 message.competitorPeriod1
    ++ (encodeUInt 2 message.solicitorPeriod1
    ++ (Alpha.encode message.modCxlBy1
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode1
    ++ (Alpha.encode message.startAlpha1
    ++ (Alpha.encode message.endAlpha1
    ++ (encodeUInt 4 message.token1
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.opBrokerId1
    ++ (Alpha.encode message.fillerx1
    ++ (Alpha.encode message.fillerOptions1
    ++ (Alpha.encode message.fillery1
    ++ (encodeUInt 2 message.orderType1
    ++ (Alpha.encode message.orderNumber1
    ++ (Alpha.encode message.accountNumber1
    ++ (encodeUInt 2 message.bookType1
    ++ (encodeUInt 2 message.buySell1
    ++ (encodeUInt 4 message.disclosedVol1
    ++ (encodeUInt 4 message.disclosedVolRemaining1
    ++ (encodeUInt 4 message.totalVolRemaining1
    ++ (encodeUInt 4 message.volume1
    ++ (encodeUInt 4 message.volumeFilledToday1
    ++ (encodeUInt 4 message.price1
    ++ (encodeUInt 4 message.triggerPrice1
    ++ (encodeUInt 4 message.goodTillDate1
    ++ (encodeUInt 4 message.entryDateTime1
    ++ (encodeUInt 4 message.minFillAon1
    ++ (encodeUInt 4 message.lastModified1
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId1
    ++ (encodeUInt 4 message.traderId1
    ++ (Alpha.encode message.brokerId1
    ++ (Alpha.encode message.cOrdFiller
    ++ (Alpha.encode message.openClose1
    ++ (Alpha.encode message.settlor1
    ++ (encodeUInt 2 message.proClient1
    ++ (encodeUInt 2 message.settlementPeriod1
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.giveupFlag1
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.filler17
    ++ (Alpha.encode message.filler18
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.mktReplay
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.secondReserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 4 message.priceDiff
    ++ (MsSpdLegInfoLeg2.encode message.msSpdLegInfoLeg2
    ++ (MsSpdLegInfoLeg3.encode message.msSpdLegInfoLeg3))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ThrlOrderErrorMessage × List UInt8) := do
  let (participantType1, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod1, bytes) ← decodeUInt 2 bytes
  let (modCxlBy1, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode1, bytes) ← decodeUInt 2 bytes
  let (startAlpha1, bytes) ← Alpha.decode 2 bytes
  let (endAlpha1, bytes) ← Alpha.decode 2 bytes
  let (token1, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (opBrokerId1, bytes) ← Alpha.decode 5 bytes
  let (fillerx1, bytes) ← Alpha.decode 1 bytes
  let (fillerOptions1, bytes) ← Alpha.decode 3 bytes
  let (fillery1, bytes) ← Alpha.decode 1 bytes
  let (orderType1, bytes) ← decodeUInt 2 bytes
  let (orderNumber1, bytes) ← Alpha.decode 8 bytes
  let (accountNumber1, bytes) ← Alpha.decode 10 bytes
  let (bookType1, bytes) ← decodeUInt 2 bytes
  let (buySell1, bytes) ← decodeUInt 2 bytes
  let (disclosedVol1, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining1, bytes) ← decodeUInt 4 bytes
  let (volume1, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday1, bytes) ← decodeUInt 4 bytes
  let (price1, bytes) ← decodeUInt 4 bytes
  let (triggerPrice1, bytes) ← decodeUInt 4 bytes
  let (goodTillDate1, bytes) ← decodeUInt 4 bytes
  let (entryDateTime1, bytes) ← decodeUInt 4 bytes
  let (minFillAon1, bytes) ← decodeUInt 4 bytes
  let (lastModified1, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId1, bytes) ← decodeUInt 2 bytes
  let (traderId1, bytes) ← decodeUInt 4 bytes
  let (brokerId1, bytes) ← Alpha.decode 5 bytes
  let (cOrdFiller, bytes) ← Alpha.decode 24 bytes
  let (openClose1, bytes) ← Alpha.decode 1 bytes
  let (settlor1, bytes) ← Alpha.decode 12 bytes
  let (proClient1, bytes) ← decodeUInt 2 bytes
  let (settlementPeriod1, bytes) ← decodeUInt 2 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (giveupFlag1, bytes) ← Alpha.decode 1 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (filler17, bytes) ← Alpha.decode 1 bytes
  let (filler18, bytes) ← Alpha.decode 1 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (mktReplay, bytes) ← Alpha.decode 8 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (secondReserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (priceDiff, bytes) ← decodeUInt 4 bytes
  let (msSpdLegInfoLeg2, bytes) ← MsSpdLegInfoLeg2.decode bytes
  let (msSpdLegInfoLeg3, bytes) ← MsSpdLegInfoLeg3.decode bytes
  pure ({ participantType1, filler1, competitorPeriod1, solicitorPeriod1, modCxlBy1, filler9, reasonCode1, startAlpha1, endAlpha1, token1, contractDesc, opBrokerId1, fillerx1, fillerOptions1, fillery1, orderType1, orderNumber1, accountNumber1, bookType1, buySell1, disclosedVol1, disclosedVolRemaining1, totalVolRemaining1, volume1, volumeFilledToday1, price1, triggerPrice1, goodTillDate1, entryDateTime1, minFillAon1, lastModified1, stOrderFlags, branchId1, traderId1, brokerId1, cOrdFiller, openClose1, settlor1, proClient1, settlementPeriod1, additionalOrderFlags, giveupFlag1, reserved2, filler17, filler18, nnfField, mktReplay, pan, algoId, secondReserved2, lastActivityReference, reserved52, priceDiff, msSpdLegInfoLeg2, msSpdLegInfoLeg3 }, bytes)

@[simp] theorem encode_length (message : ThrlOrderErrorMessage) : (encode message).length = 440 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length, MsSpdLegInfoLeg2.encode_length, MsSpdLegInfoLeg3.encode_length]

theorem encode_length_pos (message : ThrlOrderErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ThrlOrderErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MsSpdLegInfoLeg2.decode_encode, some_bind]
  dsimp only
  rw [MsSpdLegInfoLeg3.decode_encode, some_bind]
  rfl

end ThrlOrderErrorMessage

/-- On Stop Notification Message: 256 bytes -/
structure OnStopNotificationMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OnStopNotificationMessage

def encode (message : OnStopNotificationMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OnStopNotificationMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OnStopNotificationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OnStopNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OnStopNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OnStopNotificationMessage

/-- Trade Confirmation Message: 256 bytes -/
structure TradeConfirmationMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeConfirmationMessage

def encode (message : TradeConfirmationMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeConfirmationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeConfirmationMessage

/-- Trade Cancel Confirm Message: 256 bytes -/
structure TradeCancelConfirmMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeCancelConfirmMessage

def encode (message : TradeCancelConfirmMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCancelConfirmMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeCancelConfirmMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCancelConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelConfirmMessage

/-- Trade Cancel Reject Message: 256 bytes -/
structure TradeCancelRejectMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeCancelRejectMessage

def encode (message : TradeCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeCancelRejectMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeCancelRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelRejectMessage

/-- Trade Modify Reject Message: 256 bytes -/
structure TradeModifyRejectMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeModifyRejectMessage

def encode (message : TradeModifyRejectMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeModifyRejectMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeModifyRejectMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeModifyRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeModifyRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModifyRejectMessage

/-- Trade Error Message: 194 bytes -/
structure TradeErrorMessage where
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  mktType : Alpha 1
  buyOpenClose : Alpha 1
  newVolume : BitVec 32
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : Alpha 1
  sellOpenClose : Alpha 1
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  buyParticipant : Alpha 12
  sellParticipant : Alpha 12
  reserved2 : Alpha 2
  buyGiveupFlag : Alpha 1
  sellGiveupFlag : Alpha 1
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeErrorMessage

def encode (message : TradeErrorMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.mktType
    ++ (Alpha.encode message.buyOpenClose
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.requestedBy
    ++ (Alpha.encode message.sellOpenClose
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.buyParticipant
    ++ (Alpha.encode message.sellParticipant
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.buyGiveupFlag
    ++ (Alpha.encode message.sellGiveupFlag
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeErrorMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (mktType, bytes) ← Alpha.decode 1 bytes
  let (buyOpenClose, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← Alpha.decode 1 bytes
  let (sellOpenClose, bytes) ← Alpha.decode 1 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (buyParticipant, bytes) ← Alpha.decode 12 bytes
  let (sellParticipant, bytes) ← Alpha.decode 12 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (buyGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (sellGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ tokenNo, contractDesc, fillNumber, fillQuantity, fillPrice, mktType, buyOpenClose, newVolume, buyBrokerId, sellBrokerId, traderId, requestedBy, sellOpenClose, buyAccountNumber, sellAccountNumber, buyParticipant, sellParticipant, reserved2, buyGiveupFlag, sellGiveupFlag, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeErrorMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeErrorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeErrorMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeErrorMessage

/-- Trade Cancel Out Message: 194 bytes -/
structure TradeCancelOutMessage where
  tokenNo : BitVec 32
  contractDesc : ContractDesc
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  mktType : Alpha 1
  buyOpenClose : Alpha 1
  newVolume : BitVec 32
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : Alpha 1
  sellOpenClose : Alpha 1
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  buyParticipant : Alpha 12
  sellParticipant : Alpha 12
  reserved2 : Alpha 2
  buyGiveupFlag : Alpha 1
  sellGiveupFlag : Alpha 1
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeCancelOutMessage

def encode (message : TradeCancelOutMessage) : List UInt8 :=
  encodeUInt 4 message.tokenNo
    ++ (ContractDesc.encode message.contractDesc
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (Alpha.encode message.mktType
    ++ (Alpha.encode message.buyOpenClose
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.requestedBy
    ++ (Alpha.encode message.sellOpenClose
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.buyParticipant
    ++ (Alpha.encode message.sellParticipant
    ++ (Alpha.encode message.reserved2
    ++ (Alpha.encode message.buyGiveupFlag
    ++ (Alpha.encode message.sellGiveupFlag
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeCancelOutMessage × List UInt8) := do
  let (tokenNo, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (mktType, bytes) ← Alpha.decode 1 bytes
  let (buyOpenClose, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← Alpha.decode 1 bytes
  let (sellOpenClose, bytes) ← Alpha.decode 1 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (buyParticipant, bytes) ← Alpha.decode 12 bytes
  let (sellParticipant, bytes) ← Alpha.decode 12 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (buyGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (sellGiveupFlag, bytes) ← Alpha.decode 1 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ tokenNo, contractDesc, fillNumber, fillQuantity, fillPrice, mktType, buyOpenClose, newVolume, buyBrokerId, sellBrokerId, traderId, requestedBy, sellOpenClose, buyAccountNumber, sellAccountNumber, buyParticipant, sellParticipant, reserved2, buyGiveupFlag, sellGiveupFlag, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeCancelOutMessage) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ContractDesc.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancelOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelOutMessage

/-- Trade Modify Confirm Message: 256 bytes -/
structure TradeModifyConfirmMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNumber : BitVec 32
  accountNumber : Alpha 10
  buySellIndicator : BitVec 16
  originalVolume : BitVec 32
  disclosedVolume : BitVec 32
  remainingVolume : BitVec 32
  disclosedVolumeRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  goodTillDate : BitVec 32
  fillNumber : BitVec 32
  fillQuantity : BitVec 32
  fillPrice : BitVec 32
  volumeFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  counterTraderOrderNumber : Alpha 8
  counterBrokerId : Alpha 5
  secondReserved1 : Alpha 1
  token : BitVec 32
  contractDesc : ContractDesc
  openClose : Alpha 1
  oldOpenClose : Alpha 1
  bookTypeChar1 : Alpha 1
  thirdReserved1 : Alpha 1
  newVolume : BitVec 32
  oldAccountNumber : Alpha 10
  participant : Alpha 12
  oldParticipant : Alpha 12
  additionalOrderFlags : BitVec 8
  fourthReserved1 : Alpha 1
  giveUpTrade : Alpha 1
  fifthReserved1 : Alpha 1
  pan : Alpha 10
  oldPan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace TradeModifyConfirmMessage

def encode (message : TradeModifyConfirmMessage) : List UInt8 :=
  Alpha.encode message.responseOrderNumber
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.traderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.buySellIndicator
    ++ (encodeUInt 4 message.originalVolume
    ++ (encodeUInt 4 message.disclosedVolume
    ++ (encodeUInt 4 message.remainingVolume
    ++ (encodeUInt 4 message.disclosedVolumeRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQuantity
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.counterTraderOrderNumber
    ++ (Alpha.encode message.counterBrokerId
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.token
    ++ (ContractDesc.encode message.contractDesc
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.oldOpenClose
    ++ (Alpha.encode message.bookTypeChar1
    ++ (Alpha.encode message.thirdReserved1
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.oldAccountNumber
    ++ (Alpha.encode message.participant
    ++ (Alpha.encode message.oldParticipant
    ++ (encodeUIntLE 1 message.additionalOrderFlags
    ++ (Alpha.encode message.fourthReserved1
    ++ (Alpha.encode message.giveUpTrade
    ++ (Alpha.encode message.fifthReserved1
    ++ (Alpha.encode message.pan
    ++ (Alpha.encode message.oldPan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52)))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeModifyConfirmMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNumber, bytes) ← decodeUInt 4 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (buySellIndicator, bytes) ← decodeUInt 2 bytes
  let (originalVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolume, bytes) ← decodeUInt 4 bytes
  let (remainingVolume, bytes) ← decodeUInt 4 bytes
  let (disclosedVolumeRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQuantity, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (counterTraderOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (counterBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← decodeUInt 4 bytes
  let (contractDesc, bytes) ← ContractDesc.decode bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (oldOpenClose, bytes) ← Alpha.decode 1 bytes
  let (bookTypeChar1, bytes) ← Alpha.decode 1 bytes
  let (thirdReserved1, bytes) ← Alpha.decode 1 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (oldAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (participant, bytes) ← Alpha.decode 12 bytes
  let (oldParticipant, bytes) ← Alpha.decode 12 bytes
  let (additionalOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (fourthReserved1, bytes) ← Alpha.decode 1 bytes
  let (giveUpTrade, bytes) ← Alpha.decode 1 bytes
  let (fifthReserved1, bytes) ← Alpha.decode 1 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (oldPan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNumber, accountNumber, buySellIndicator, originalVolume, disclosedVolume, remainingVolume, disclosedVolumeRemaining, price, stOrderFlags, goodTillDate, fillNumber, fillQuantity, fillPrice, volumeFilledToday, activityType, activityTime, counterTraderOrderNumber, counterBrokerId, secondReserved1, token, contractDesc, openClose, oldOpenClose, bookTypeChar1, thirdReserved1, newVolume, oldAccountNumber, participant, oldParticipant, additionalOrderFlags, fourthReserved1, giveUpTrade, fifthReserved1, pan, oldPan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeModifyConfirmMessage) : (encode message).length = 256 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, ContractDesc.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeModifyConfirmMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeModifyConfirmMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContractDesc.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeModifyConfirmMessage

/-- Sign On Request Out Message: 238 bytes -/
structure SignOnRequestOutMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  batch2StartTime : BitVec 32
  hostSwitchContext : Alpha 1
  colour : Alpha 50
  secondReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : Alpha 1
  brokerName : Alpha 25
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOnRequestOutMessage

def encode (message : SignOnRequestOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.batch2StartTime
    ++ (Alpha.encode message.hostSwitchContext
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (Alpha.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SignOnRequestOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (batch2StartTime, bytes) ← decodeUInt 4 bytes
  let (hostSwitchContext, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← Alpha.decode 1 bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, batch2StartTime, hostSwitchContext, colour, secondReserved1, userType, sequenceNumber, wsClassName, brokerStatus, showIndex, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnRequestOutMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnRequestOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SignOnRequestOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end SignOnRequestOutMessage

/-- Sign Off Trader Out Message: 238 bytes -/
structure SignOffTraderOutMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDate : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  batch2StartTime : BitVec 32
  hostSwitchContext : Alpha 1
  colour : Alpha 50
  secondReserved1 : Alpha 1
  userType : BitVec 16
  sequenceNumber : Alpha 8
  wsClassName : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  stBrokerEligibilityPerMkt : BitVec 16
  memberType : BitVec 16
  clearingStatus : Alpha 1
  brokerName : Alpha 25
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOffTraderOutMessage

def encode (message : SignOffTraderOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.secondReserved8
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.traderName
    ++ (encodeUInt 4 message.lastPasswordChangeDate
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (encodeUInt 4 message.batch2StartTime
    ++ (Alpha.encode message.hostSwitchContext
    ++ (Alpha.encode message.colour
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.wsClassName
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.stBrokerEligibilityPerMkt
    ++ (encodeUInt 2 message.memberType
    ++ (Alpha.encode message.clearingStatus
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SignOffTraderOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDate, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (batch2StartTime, bytes) ← decodeUInt 4 bytes
  let (hostSwitchContext, bytes) ← Alpha.decode 1 bytes
  let (colour, bytes) ← Alpha.decode 50 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (wsClassName, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (stBrokerEligibilityPerMkt, bytes) ← decodeUInt 2 bytes
  let (memberType, bytes) ← decodeUInt 2 bytes
  let (clearingStatus, bytes) ← Alpha.decode 1 bytes
  let (brokerName, bytes) ← Alpha.decode 25 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, batch2StartTime, hostSwitchContext, colour, secondReserved1, userType, sequenceNumber, wsClassName, brokerStatus, showIndex, stBrokerEligibilityPerMkt, memberType, clearingStatus, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOffTraderOutMessage) : (encode message).length = 238 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOffTraderOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SignOffTraderOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end SignOffTraderOutMessage

/-- Error Response Out Message: 142 bytes -/
structure ErrorResponseOutMessage where
  key : Alpha 14
  errorMessage : Alpha 128
  deriving DecidableEq, Repr

namespace ErrorResponseOutMessage

def encode (message : ErrorResponseOutMessage) : List UInt8 :=
  Alpha.encode message.key
    ++ (Alpha.encode message.errorMessage)

def decode (bytes : List UInt8) : Option (ErrorResponseOutMessage × List UInt8) := do
  let (key, bytes) ← Alpha.decode 14 bytes
  let (errorMessage, bytes) ← Alpha.decode 128 bytes
  pure ({ key, errorMessage }, bytes)

@[simp] theorem encode_length (message : ErrorResponseOutMessage) : (encode message).length = 142 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ErrorResponseOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorResponseOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorResponseOutMessage

/-- Gr Response Message: 84 bytes -/
structure GrResponseMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  ipAddress : Alpha 16
  port : BitVec 32
  sessionKey : Alpha 8
  cryptographicKey : Alpha 32
  cryptographicIv : Alpha 16
  deriving DecidableEq, Repr

namespace GrResponseMessage

def encode (message : GrResponseMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.ipAddress
    ++ (encodeUInt 4 message.port
    ++ (Alpha.encode message.sessionKey
    ++ (Alpha.encode message.cryptographicKey
    ++ (Alpha.encode message.cryptographicIv)))))))

def decode (bytes : List UInt8) : Option (GrResponseMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (ipAddress, bytes) ← Alpha.decode 16 bytes
  let (port, bytes) ← decodeUInt 4 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  let (cryptographicKey, bytes) ← Alpha.decode 32 bytes
  let (cryptographicIv, bytes) ← Alpha.decode 16 bytes
  pure ({ boxId, brokerId, filler, ipAddress, port, sessionKey, cryptographicKey, cryptographicIv }, bytes)

@[simp] theorem encode_length (message : GrResponseMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : GrResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GrResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GrResponseMessage

/-- User Addr Unlock Confirm Out Message: 40 bytes -/
structure UserAddrUnlockConfirmOutMessage where
  userId : BitVec 32
  reserved36 : Alpha 36
  deriving DecidableEq, Repr

namespace UserAddrUnlockConfirmOutMessage

def encode (message : UserAddrUnlockConfirmOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved36)

def decode (bytes : List UInt8) : Option (UserAddrUnlockConfirmOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved36, bytes) ← Alpha.decode 36 bytes
  pure ({ userId, reserved36 }, bytes)

@[simp] theorem encode_length (message : UserAddrUnlockConfirmOutMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddrUnlockConfirmOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddrUnlockConfirmOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserAddrUnlockConfirmOutMessage

/-- User Addr Unlock Approve Out Message: 40 bytes -/
structure UserAddrUnlockApproveOutMessage where
  userId : BitVec 32
  reserved36 : Alpha 36
  deriving DecidableEq, Repr

namespace UserAddrUnlockApproveOutMessage

def encode (message : UserAddrUnlockApproveOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved36)

def decode (bytes : List UInt8) : Option (UserAddrUnlockApproveOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved36, bytes) ← Alpha.decode 36 bytes
  pure ({ userId, reserved36 }, bytes)

@[simp] theorem encode_length (message : UserAddrUnlockApproveOutMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddrUnlockApproveOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddrUnlockApproveOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserAddrUnlockApproveOutMessage

/-- User Addr Unlock Reject Out Message: 40 bytes -/
structure UserAddrUnlockRejectOutMessage where
  userId : BitVec 32
  reserved36 : Alpha 36
  deriving DecidableEq, Repr

namespace UserAddrUnlockRejectOutMessage

def encode (message : UserAddrUnlockRejectOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved36)

def decode (bytes : List UInt8) : Option (UserAddrUnlockRejectOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved36, bytes) ← Alpha.decode 36 bytes
  pure ({ userId, reserved36 }, bytes)

@[simp] theorem encode_length (message : UserAddrUnlockRejectOutMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : UserAddrUnlockRejectOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserAddrUnlockRejectOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserAddrUnlockRejectOutMessage

/-- Branch Limits 1: 32 bytes -/
structure BranchLimits1 where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace BranchLimits1

def encode (message : BranchLimits1) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (BranchLimits1 × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : BranchLimits1) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimits1) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimits1) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimits1

/-- Branch Limits 2: 32 bytes -/
structure BranchLimits2 where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace BranchLimits2

def encode (message : BranchLimits2) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (BranchLimits2 × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, reserved16 }, bytes)

@[simp] theorem encode_length (message : BranchLimits2) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimits2) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimits2) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimits2

/-- Branch Ord Val Limit Update Ou Message: 96 bytes -/
structure BranchOrdValLimitUpdateOuMessage where
  brokerId : Alpha 5
  reserved25 : Alpha 25
  branchId : BitVec 16
  branchLimits1 : BranchLimits1
  branchLimits2 : BranchLimits2
  deriving DecidableEq, Repr

namespace BranchOrdValLimitUpdateOuMessage

def encode (message : BranchOrdValLimitUpdateOuMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved25
    ++ (encodeUInt 2 message.branchId
    ++ (BranchLimits1.encode message.branchLimits1
    ++ (BranchLimits2.encode message.branchLimits2))))

def decode (bytes : List UInt8) : Option (BranchOrdValLimitUpdateOuMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved25, bytes) ← Alpha.decode 25 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (branchLimits1, bytes) ← BranchLimits1.decode bytes
  let (branchLimits2, bytes) ← BranchLimits2.decode bytes
  pure ({ brokerId, reserved25, branchId, branchLimits1, branchLimits2 }, bytes)

@[simp] theorem encode_length (message : BranchOrdValLimitUpdateOuMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, BranchLimits1.encode_length, BranchLimits2.encode_length]

theorem encode_length_pos (message : BranchOrdValLimitUpdateOuMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrdValLimitUpdateOuMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BranchLimits1.decode_encode, some_bind]
  dsimp only
  rw [BranchLimits2.decode_encode, some_bind]
  rfl

end BranchOrdValLimitUpdateOuMessage

/-- Instrument User: 64 bytes -/
structure InstrumentUser where
  branchBuyValueLimit : Alpha 8
  branchSellValueLimit : Alpha 8
  branchUsedBuyValueLimit : Alpha 8
  branchUsedSellValueLimit : Alpha 8
  userOrderBuyValueLimit : Alpha 8
  userOrderSellValueLimit : Alpha 8
  userOrderUsedBuyValueLimit : Alpha 8
  userOrderUsedSellValueLimit : Alpha 8
  deriving DecidableEq, Repr

namespace InstrumentUser

def encode (message : InstrumentUser) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.branchUsedBuyValueLimit
    ++ (Alpha.encode message.branchUsedSellValueLimit
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.userOrderUsedBuyValueLimit
    ++ (Alpha.encode message.userOrderUsedSellValueLimit)))))))

def decode (bytes : List UInt8) : Option (InstrumentUser × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchUsedBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (branchUsedSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderUsedBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (userOrderUsedSellValueLimit, bytes) ← Alpha.decode 8 bytes
  pure ({ branchBuyValueLimit, branchSellValueLimit, branchUsedBuyValueLimit, branchUsedSellValueLimit, userOrderBuyValueLimit, userOrderSellValueLimit, userOrderUsedBuyValueLimit, userOrderUsedSellValueLimit }, bytes)

@[simp] theorem encode_length (message : InstrumentUser) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentUser) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentUser) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentUser

/-- User Order Limit Update Out Message: 166 bytes -/
structure UserOrderLimitUpdateOutMessage where
  brokerId : Alpha 5
  branchId : BitVec 16
  userName : Alpha 25
  userId : BitVec 32
  userType : BitVec 16
  instrumentUser : InstrumentUser
  reserved64 : Alpha 64
  deriving DecidableEq, Repr

namespace UserOrderLimitUpdateOutMessage

def encode (message : UserOrderLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (encodeUInt 2 message.branchId
    ++ (Alpha.encode message.userName
    ++ (encodeUInt 4 message.userId
    ++ (encodeUInt 2 message.userType
    ++ (InstrumentUser.encode message.instrumentUser
    ++ (Alpha.encode message.reserved64))))))

def decode (bytes : List UInt8) : Option (UserOrderLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (userName, bytes) ← Alpha.decode 25 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (instrumentUser, bytes) ← InstrumentUser.decode bytes
  let (reserved64, bytes) ← Alpha.decode 64 bytes
  pure ({ brokerId, branchId, userName, userId, userType, instrumentUser, reserved64 }, bytes)

@[simp] theorem encode_length (message : UserOrderLimitUpdateOutMessage) : (encode message).length = 166 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, InstrumentUser.encode_length]

theorem encode_length_pos (message : UserOrderLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentUser.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserOrderLimitUpdateOutMessage

/-- Dealer Limit Update Out Message: 26 bytes -/
structure DealerLimitUpdateOutMessage where
  brokerId : Alpha 5
  userId : BitVec 32
  ordQtyBuff : Alpha 8
  ordValBuff : Alpha 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace DealerLimitUpdateOutMessage

def encode (message : DealerLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.ordQtyBuff
    ++ (Alpha.encode message.ordValBuff
    ++ (Alpha.encode message.reserved1))))

def decode (bytes : List UInt8) : Option (DealerLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (ordQtyBuff, bytes) ← Alpha.decode 8 bytes
  let (ordValBuff, bytes) ← Alpha.decode 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ brokerId, userId, ordQtyBuff, ordValBuff, reserved1 }, bytes)

@[simp] theorem encode_length (message : DealerLimitUpdateOutMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DealerLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DealerLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DealerLimitUpdateOutMessage

/-- Reset User Password Out Message: 18 bytes -/
structure ResetUserPasswordOutMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace ResetUserPasswordOutMessage

def encode (message : ResetUserPasswordOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (ResetUserPasswordOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : ResetUserPasswordOutMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResetUserPasswordOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetUserPasswordOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResetUserPasswordOutMessage

/-- Col User Status Change Out Message: 6 bytes -/
structure ColUserStatusChangeOutMessage where
  userId : BitVec 32
  colUserBit : Alpha 1
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace ColUserStatusChangeOutMessage

def encode (message : ColUserStatusChangeOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.colUserBit
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (ColUserStatusChangeOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (colUserBit, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, colUserBit, reserved1 }, bytes)

@[simp] theorem encode_length (message : ColUserStatusChangeOutMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ColUserStatusChangeOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ColUserStatusChangeOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ColUserStatusChangeOutMessage

/-- Spd Ord Limit Update Out Message: 26 bytes -/
structure SpdOrdLimitUpdateOutMessage where
  brokerId : Alpha 5
  userId : BitVec 32
  spdOrdQtyBuff : Alpha 8
  spdOrdValBuff : Alpha 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SpdOrdLimitUpdateOutMessage

def encode (message : SpdOrdLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.spdOrdQtyBuff
    ++ (Alpha.encode message.spdOrdValBuff
    ++ (Alpha.encode message.reserved1))))

def decode (bytes : List UInt8) : Option (SpdOrdLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (spdOrdQtyBuff, bytes) ← Alpha.decode 8 bytes
  let (spdOrdValBuff, bytes) ← Alpha.decode 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ brokerId, userId, spdOrdQtyBuff, spdOrdValBuff, reserved1 }, bytes)

@[simp] theorem encode_length (message : SpdOrdLimitUpdateOutMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpdOrdLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpdOrdLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpdOrdLimitUpdateOutMessage

/-- Header Record Message: 0 bytes -/
structure HeaderRecordMessage where
  deriving DecidableEq, Repr

namespace HeaderRecordMessage

def encode (_ : HeaderRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeaderRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeaderRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeaderRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeaderRecordMessage

/-- Message Record Message: 0 bytes -/
structure MessageRecordMessage where
  deriving DecidableEq, Repr

namespace MessageRecordMessage

def encode (_ : MessageRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (MessageRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : MessageRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : MessageRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end MessageRecordMessage

/-- Trailer Record Message: 0 bytes -/
structure TrailerRecordMessage where
  deriving DecidableEq, Repr

namespace TrailerRecordMessage

def encode (_ : TrailerRecordMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TrailerRecordMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TrailerRecordMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TrailerRecordMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end TrailerRecordMessage

/-- Update Localdb Header Message: 2 bytes -/
structure UpdateLocaldbHeaderMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocaldbHeaderMessage

def encode (message : UpdateLocaldbHeaderMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocaldbHeaderMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocaldbHeaderMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocaldbHeaderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocaldbHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UpdateLocaldbHeaderMessage

/-- Update Localdb Trailer Message: 2 bytes -/
structure UpdateLocaldbTrailerMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocaldbTrailerMessage

def encode (message : UpdateLocaldbTrailerMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocaldbTrailerMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocaldbTrailerMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocaldbTrailerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocaldbTrailerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end UpdateLocaldbTrailerMessage

/-- Bcast Asset Mstr Chg Message: 392 bytes -/
structure BcastAssetMstrChgMessage where
  noOfRecords : BitVec 16
  reserved390 : Alpha 390
  deriving DecidableEq, Repr

namespace BcastAssetMstrChgMessage

def encode (message : BcastAssetMstrChgMessage) : List UInt8 :=
  encodeUInt 2 message.noOfRecords
    ++ (Alpha.encode message.reserved390)

def decode (bytes : List UInt8) : Option (BcastAssetMstrChgMessage × List UInt8) := do
  let (noOfRecords, bytes) ← decodeUInt 2 bytes
  let (reserved390, bytes) ← Alpha.decode 390 bytes
  pure ({ noOfRecords, reserved390 }, bytes)

@[simp] theorem encode_length (message : BcastAssetMstrChgMessage) : (encode message).length = 392 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BcastAssetMstrChgMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BcastAssetMstrChgMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BcastAssetMstrChgMessage

/-- Box Sign On Request Out Message: 12 bytes -/
structure BoxSignOnRequestOutMessage where
  boxId : BitVec 16
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace BoxSignOnRequestOutMessage

def encode (message : BoxSignOnRequestOutMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.reserved10)

def decode (bytes : List UInt8) : Option (BoxSignOnRequestOutMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ boxId, reserved10 }, bytes)

@[simp] theorem encode_length (message : BoxSignOnRequestOutMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnRequestOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnRequestOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BoxSignOnRequestOutMessage

/-- Secure Box Registration Response Out Message: 0 bytes -/
structure SecureBoxRegistrationResponseOutMessage where
  deriving DecidableEq, Repr

namespace SecureBoxRegistrationResponseOutMessage

def encode (_ : SecureBoxRegistrationResponseOutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SecureBoxRegistrationResponseOutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SecureBoxRegistrationResponseOutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecureBoxRegistrationResponseOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SecureBoxRegistrationResponseOutMessage

/-- Box Sign Off Message: 2 bytes -/
structure BoxSignOffMessage where
  boxId : BitVec 16
  deriving DecidableEq, Repr

namespace BoxSignOffMessage

def encode (message : BoxSignOffMessage) : List UInt8 :=
  encodeUInt 2 message.boxId

def decode (bytes : List UInt8) : Option (BoxSignOffMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  pure ({ boxId }, bytes)

@[simp] theorem encode_length (message : BoxSignOffMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : BoxSignOffMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOffMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BoxSignOffMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | systemInformationOutMessage (message : SystemInformationOutMessage) -- 1601
  | partialSystemInformationMessage (message : PartialSystemInformationMessage) -- 7321
  | openOrderReportMessage (message : OpenOrderReportMessage) -- 1821
  | spreadOrderLogReportMessage (message : SpreadOrderLogReportMessage) -- 1992
  | spreadTradeReportMessage (message : SpreadTradeReportMessage) -- 1993
  | boardLotOutMessage (message : BoardLotOutMessage) -- 2001
  | negOrderToBlMessage (message : NegOrderToBlMessage) -- 2008
  | orderModOutMessage (message : OrderModOutMessage) -- 2041
  | orderModRejectMessage (message : OrderModRejectMessage) -- 2042
  | orderCancelOutMessage (message : OrderCancelOutMessage) -- 2071
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 2072
  | orderConfirmationMessage (message : OrderConfirmationMessage) -- 2073
  | orderModConfirmationMessage (message : OrderModConfirmationMessage) -- 2074
  | orderCancelConfirmationMessage (message : OrderCancelConfirmationMessage) -- 2075
  | cancelNegOrderMessage (message : CancelNegOrderMessage) -- 2076
  | freezeToControlMessage (message : FreezeToControlMessage) -- 2170
  | orderErrorMessage (message : OrderErrorMessage) -- 2231
  | batchOrderCancelMessage (message : BatchOrderCancelMessage) -- 9002
  | spBoardLotOutMessage (message : SpBoardLotOutMessage) -- 2101
  | twolBoardLotOutMessage (message : TwolBoardLotOutMessage) -- 2103
  | thrlBoardLotOutMessage (message : ThrlBoardLotOutMessage) -- 2105
  | spOrderCancelOutMessage (message : SpOrderCancelOutMessage) -- 2107
  | spOrderModOutMessage (message : SpOrderModOutMessage) -- 2119
  | spOrderConfirmationMessage (message : SpOrderConfirmationMessage) -- 2124
  | twolOrderConfirmationMessage (message : TwolOrderConfirmationMessage) -- 2125
  | thrlOrderConfirmationMessage (message : ThrlOrderConfirmationMessage) -- 2126
  | spOrderCxlRejOutMessage (message : SpOrderCxlRejOutMessage) -- 2127
  | spOrderCxlConfirmationMessage (message : SpOrderCxlConfirmationMessage) -- 2130
  | twolOrderCxlConfirmationMessage (message : TwolOrderCxlConfirmationMessage) -- 2131
  | thrlOrderCxlConfirmationMessage (message : ThrlOrderCxlConfirmationMessage) -- 2132
  | spOrderModRejOutMessage (message : SpOrderModRejOutMessage) -- 2133
  | spOrderModConOutMessage (message : SpOrderModConOutMessage) -- 2136
  | twolOrderErrorMessage (message : TwolOrderErrorMessage) -- 2155
  | thrlOrderErrorMessage (message : ThrlOrderErrorMessage) -- 2156
  | onStopNotificationMessage (message : OnStopNotificationMessage) -- 2212
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2222
  | tradeCancelConfirmMessage (message : TradeCancelConfirmMessage) -- 2282
  | tradeCancelRejectMessage (message : TradeCancelRejectMessage) -- 2286
  | tradeModifyRejectMessage (message : TradeModifyRejectMessage) -- 2288
  | tradeErrorMessage (message : TradeErrorMessage) -- 2223
  | tradeCancelOutMessage (message : TradeCancelOutMessage) -- 5441
  | tradeModifyConfirmMessage (message : TradeModifyConfirmMessage) -- 2287
  | signOnRequestOutMessage (message : SignOnRequestOutMessage) -- 2301
  | signOffTraderOutMessage (message : SignOffTraderOutMessage) -- 5585
  | errorResponseOutMessage (message : ErrorResponseOutMessage) -- 2302
  | grResponseMessage (message : GrResponseMessage) -- 2401
  | userAddrUnlockConfirmOutMessage (message : UserAddrUnlockConfirmOutMessage) -- 5428
  | userAddrUnlockApproveOutMessage (message : UserAddrUnlockApproveOutMessage) -- 5483
  | userAddrUnlockRejectOutMessage (message : UserAddrUnlockRejectOutMessage) -- 5484
  | branchOrdValLimitUpdateOuMessage (message : BranchOrdValLimitUpdateOuMessage) -- 5717
  | userOrderLimitUpdateOutMessage (message : UserOrderLimitUpdateOutMessage) -- 5731
  | dealerLimitUpdateOutMessage (message : DealerLimitUpdateOutMessage) -- 5733
  | resetUserPasswordOutMessage (message : ResetUserPasswordOutMessage) -- 5741
  | colUserStatusChangeOutMessage (message : ColUserStatusChangeOutMessage) -- 5745
  | spdOrdLimitUpdateOutMessage (message : SpdOrdLimitUpdateOutMessage) -- 5772
  | headerRecordMessage (message : HeaderRecordMessage) -- 7011
  | messageRecordMessage (message : MessageRecordMessage) -- 7021
  | trailerRecordMessage (message : TrailerRecordMessage) -- 7031
  | updateLocaldbHeaderMessage (message : UpdateLocaldbHeaderMessage) -- 7307
  | updateLocaldbTrailerMessage (message : UpdateLocaldbTrailerMessage) -- 7308
  | bcastAssetMstrChgMessage (message : BcastAssetMstrChgMessage) -- 7325
  | boxSignOnRequestOutMessage (message : BoxSignOnRequestOutMessage) -- 23001
  | secureBoxRegistrationResponseOutMessage (message : SecureBoxRegistrationResponseOutMessage) -- 23009
  | boxSignOffMessage (message : BoxSignOffMessage) -- 20322
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .systemInformationOutMessage _ => 1601
  | .partialSystemInformationMessage _ => 7321
  | .openOrderReportMessage _ => 1821
  | .spreadOrderLogReportMessage _ => 1992
  | .spreadTradeReportMessage _ => 1993
  | .boardLotOutMessage _ => 2001
  | .negOrderToBlMessage _ => 2008
  | .orderModOutMessage _ => 2041
  | .orderModRejectMessage _ => 2042
  | .orderCancelOutMessage _ => 2071
  | .orderCancelRejectMessage _ => 2072
  | .orderConfirmationMessage _ => 2073
  | .orderModConfirmationMessage _ => 2074
  | .orderCancelConfirmationMessage _ => 2075
  | .cancelNegOrderMessage _ => 2076
  | .freezeToControlMessage _ => 2170
  | .orderErrorMessage _ => 2231
  | .batchOrderCancelMessage _ => 9002
  | .spBoardLotOutMessage _ => 2101
  | .twolBoardLotOutMessage _ => 2103
  | .thrlBoardLotOutMessage _ => 2105
  | .spOrderCancelOutMessage _ => 2107
  | .spOrderModOutMessage _ => 2119
  | .spOrderConfirmationMessage _ => 2124
  | .twolOrderConfirmationMessage _ => 2125
  | .thrlOrderConfirmationMessage _ => 2126
  | .spOrderCxlRejOutMessage _ => 2127
  | .spOrderCxlConfirmationMessage _ => 2130
  | .twolOrderCxlConfirmationMessage _ => 2131
  | .thrlOrderCxlConfirmationMessage _ => 2132
  | .spOrderModRejOutMessage _ => 2133
  | .spOrderModConOutMessage _ => 2136
  | .twolOrderErrorMessage _ => 2155
  | .thrlOrderErrorMessage _ => 2156
  | .onStopNotificationMessage _ => 2212
  | .tradeConfirmationMessage _ => 2222
  | .tradeCancelConfirmMessage _ => 2282
  | .tradeCancelRejectMessage _ => 2286
  | .tradeModifyRejectMessage _ => 2288
  | .tradeErrorMessage _ => 2223
  | .tradeCancelOutMessage _ => 5441
  | .tradeModifyConfirmMessage _ => 2287
  | .signOnRequestOutMessage _ => 2301
  | .signOffTraderOutMessage _ => 5585
  | .errorResponseOutMessage _ => 2302
  | .grResponseMessage _ => 2401
  | .userAddrUnlockConfirmOutMessage _ => 5428
  | .userAddrUnlockApproveOutMessage _ => 5483
  | .userAddrUnlockRejectOutMessage _ => 5484
  | .branchOrdValLimitUpdateOuMessage _ => 5717
  | .userOrderLimitUpdateOutMessage _ => 5731
  | .dealerLimitUpdateOutMessage _ => 5733
  | .resetUserPasswordOutMessage _ => 5741
  | .colUserStatusChangeOutMessage _ => 5745
  | .spdOrdLimitUpdateOutMessage _ => 5772
  | .headerRecordMessage _ => 7011
  | .messageRecordMessage _ => 7021
  | .trailerRecordMessage _ => 7031
  | .updateLocaldbHeaderMessage _ => 7307
  | .updateLocaldbTrailerMessage _ => 7308
  | .bcastAssetMstrChgMessage _ => 7325
  | .boxSignOnRequestOutMessage _ => 23001
  | .secureBoxRegistrationResponseOutMessage _ => 23009
  | .boxSignOffMessage _ => 20322

def encode : ServerMessagePayload → List UInt8
  | .systemInformationOutMessage message => SystemInformationOutMessage.encode message
  | .partialSystemInformationMessage message => PartialSystemInformationMessage.encode message
  | .openOrderReportMessage message => OpenOrderReportMessage.encode message
  | .spreadOrderLogReportMessage message => SpreadOrderLogReportMessage.encode message
  | .spreadTradeReportMessage message => SpreadTradeReportMessage.encode message
  | .boardLotOutMessage message => BoardLotOutMessage.encode message
  | .negOrderToBlMessage message => NegOrderToBlMessage.encode message
  | .orderModOutMessage message => OrderModOutMessage.encode message
  | .orderModRejectMessage message => OrderModRejectMessage.encode message
  | .orderCancelOutMessage message => OrderCancelOutMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .orderConfirmationMessage message => OrderConfirmationMessage.encode message
  | .orderModConfirmationMessage message => OrderModConfirmationMessage.encode message
  | .orderCancelConfirmationMessage message => OrderCancelConfirmationMessage.encode message
  | .cancelNegOrderMessage message => CancelNegOrderMessage.encode message
  | .freezeToControlMessage message => FreezeToControlMessage.encode message
  | .orderErrorMessage message => OrderErrorMessage.encode message
  | .batchOrderCancelMessage message => BatchOrderCancelMessage.encode message
  | .spBoardLotOutMessage message => SpBoardLotOutMessage.encode message
  | .twolBoardLotOutMessage message => TwolBoardLotOutMessage.encode message
  | .thrlBoardLotOutMessage message => ThrlBoardLotOutMessage.encode message
  | .spOrderCancelOutMessage message => SpOrderCancelOutMessage.encode message
  | .spOrderModOutMessage message => SpOrderModOutMessage.encode message
  | .spOrderConfirmationMessage message => SpOrderConfirmationMessage.encode message
  | .twolOrderConfirmationMessage message => TwolOrderConfirmationMessage.encode message
  | .thrlOrderConfirmationMessage message => ThrlOrderConfirmationMessage.encode message
  | .spOrderCxlRejOutMessage message => SpOrderCxlRejOutMessage.encode message
  | .spOrderCxlConfirmationMessage message => SpOrderCxlConfirmationMessage.encode message
  | .twolOrderCxlConfirmationMessage message => TwolOrderCxlConfirmationMessage.encode message
  | .thrlOrderCxlConfirmationMessage message => ThrlOrderCxlConfirmationMessage.encode message
  | .spOrderModRejOutMessage message => SpOrderModRejOutMessage.encode message
  | .spOrderModConOutMessage message => SpOrderModConOutMessage.encode message
  | .twolOrderErrorMessage message => TwolOrderErrorMessage.encode message
  | .thrlOrderErrorMessage message => ThrlOrderErrorMessage.encode message
  | .onStopNotificationMessage message => OnStopNotificationMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeCancelConfirmMessage message => TradeCancelConfirmMessage.encode message
  | .tradeCancelRejectMessage message => TradeCancelRejectMessage.encode message
  | .tradeModifyRejectMessage message => TradeModifyRejectMessage.encode message
  | .tradeErrorMessage message => TradeErrorMessage.encode message
  | .tradeCancelOutMessage message => TradeCancelOutMessage.encode message
  | .tradeModifyConfirmMessage message => TradeModifyConfirmMessage.encode message
  | .signOnRequestOutMessage message => SignOnRequestOutMessage.encode message
  | .signOffTraderOutMessage message => SignOffTraderOutMessage.encode message
  | .errorResponseOutMessage message => ErrorResponseOutMessage.encode message
  | .grResponseMessage message => GrResponseMessage.encode message
  | .userAddrUnlockConfirmOutMessage message => UserAddrUnlockConfirmOutMessage.encode message
  | .userAddrUnlockApproveOutMessage message => UserAddrUnlockApproveOutMessage.encode message
  | .userAddrUnlockRejectOutMessage message => UserAddrUnlockRejectOutMessage.encode message
  | .branchOrdValLimitUpdateOuMessage message => BranchOrdValLimitUpdateOuMessage.encode message
  | .userOrderLimitUpdateOutMessage message => UserOrderLimitUpdateOutMessage.encode message
  | .dealerLimitUpdateOutMessage message => DealerLimitUpdateOutMessage.encode message
  | .resetUserPasswordOutMessage message => ResetUserPasswordOutMessage.encode message
  | .colUserStatusChangeOutMessage message => ColUserStatusChangeOutMessage.encode message
  | .spdOrdLimitUpdateOutMessage message => SpdOrdLimitUpdateOutMessage.encode message
  | .headerRecordMessage message => HeaderRecordMessage.encode message
  | .messageRecordMessage message => MessageRecordMessage.encode message
  | .trailerRecordMessage message => TrailerRecordMessage.encode message
  | .updateLocaldbHeaderMessage message => UpdateLocaldbHeaderMessage.encode message
  | .updateLocaldbTrailerMessage message => UpdateLocaldbTrailerMessage.encode message
  | .bcastAssetMstrChgMessage message => BcastAssetMstrChgMessage.encode message
  | .boxSignOnRequestOutMessage message => BoxSignOnRequestOutMessage.encode message
  | .secureBoxRegistrationResponseOutMessage message => SecureBoxRegistrationResponseOutMessage.encode message
  | .boxSignOffMessage message => BoxSignOffMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerMessagePayload) : (encode message).length ≤ 440 := by
  cases message with
  | systemInformationOutMessage inner =>
    simp only [encode, SystemInformationOutMessage.encode_length]
    omega
  | partialSystemInformationMessage inner =>
    simp only [encode, PartialSystemInformationMessage.encode_length]
    omega
  | openOrderReportMessage inner =>
    simp only [encode, OpenOrderReportMessage.encode_length]
    omega
  | spreadOrderLogReportMessage inner =>
    simp only [encode, SpreadOrderLogReportMessage.encode_length]
    omega
  | spreadTradeReportMessage inner =>
    simp only [encode, SpreadTradeReportMessage.encode_length]
    omega
  | boardLotOutMessage inner =>
    simp only [encode, BoardLotOutMessage.encode_length]
    omega
  | negOrderToBlMessage inner =>
    simp only [encode, NegOrderToBlMessage.encode_length]
    omega
  | orderModOutMessage inner =>
    simp only [encode, OrderModOutMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [encode, OrderModRejectMessage.encode_length]
    omega
  | orderCancelOutMessage inner =>
    simp only [encode, OrderCancelOutMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderConfirmationMessage inner =>
    simp only [encode, OrderConfirmationMessage.encode_length]
    omega
  | orderModConfirmationMessage inner =>
    simp only [encode, OrderModConfirmationMessage.encode_length]
    omega
  | orderCancelConfirmationMessage inner =>
    simp only [encode, OrderCancelConfirmationMessage.encode_length]
    omega
  | cancelNegOrderMessage inner =>
    simp only [encode, CancelNegOrderMessage.encode_length]
    omega
  | freezeToControlMessage inner =>
    simp only [encode, FreezeToControlMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [encode, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [encode, BatchOrderCancelMessage.encode_length]
    omega
  | spBoardLotOutMessage inner =>
    simp only [encode, SpBoardLotOutMessage.encode_length]
    omega
  | twolBoardLotOutMessage inner =>
    simp only [encode, TwolBoardLotOutMessage.encode_length]
    omega
  | thrlBoardLotOutMessage inner =>
    simp only [encode, ThrlBoardLotOutMessage.encode_length]
    omega
  | spOrderCancelOutMessage inner =>
    simp only [encode, SpOrderCancelOutMessage.encode_length]
    omega
  | spOrderModOutMessage inner =>
    simp only [encode, SpOrderModOutMessage.encode_length]
    omega
  | spOrderConfirmationMessage inner =>
    simp only [encode, SpOrderConfirmationMessage.encode_length]
    omega
  | twolOrderConfirmationMessage inner =>
    simp only [encode, TwolOrderConfirmationMessage.encode_length]
    omega
  | thrlOrderConfirmationMessage inner =>
    simp only [encode, ThrlOrderConfirmationMessage.encode_length]
    omega
  | spOrderCxlRejOutMessage inner =>
    simp only [encode, SpOrderCxlRejOutMessage.encode_length]
    omega
  | spOrderCxlConfirmationMessage inner =>
    simp only [encode, SpOrderCxlConfirmationMessage.encode_length]
    omega
  | twolOrderCxlConfirmationMessage inner =>
    simp only [encode, TwolOrderCxlConfirmationMessage.encode_length]
    omega
  | thrlOrderCxlConfirmationMessage inner =>
    simp only [encode, ThrlOrderCxlConfirmationMessage.encode_length]
    omega
  | spOrderModRejOutMessage inner =>
    simp only [encode, SpOrderModRejOutMessage.encode_length]
    omega
  | spOrderModConOutMessage inner =>
    simp only [encode, SpOrderModConOutMessage.encode_length]
    omega
  | twolOrderErrorMessage inner =>
    simp only [encode, TwolOrderErrorMessage.encode_length]
    omega
  | thrlOrderErrorMessage inner =>
    simp only [encode, ThrlOrderErrorMessage.encode_length]
    omega
  | onStopNotificationMessage inner =>
    simp only [encode, OnStopNotificationMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [encode, TradeConfirmationMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [encode, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [encode, TradeCancelRejectMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [encode, TradeModifyRejectMessage.encode_length]
    omega
  | tradeErrorMessage inner =>
    simp only [encode, TradeErrorMessage.encode_length]
    omega
  | tradeCancelOutMessage inner =>
    simp only [encode, TradeCancelOutMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [encode, TradeModifyConfirmMessage.encode_length]
    omega
  | signOnRequestOutMessage inner =>
    simp only [encode, SignOnRequestOutMessage.encode_length]
    omega
  | signOffTraderOutMessage inner =>
    simp only [encode, SignOffTraderOutMessage.encode_length]
    omega
  | errorResponseOutMessage inner =>
    simp only [encode, ErrorResponseOutMessage.encode_length]
    omega
  | grResponseMessage inner =>
    simp only [encode, GrResponseMessage.encode_length]
    omega
  | userAddrUnlockConfirmOutMessage inner =>
    simp only [encode, UserAddrUnlockConfirmOutMessage.encode_length]
    omega
  | userAddrUnlockApproveOutMessage inner =>
    simp only [encode, UserAddrUnlockApproveOutMessage.encode_length]
    omega
  | userAddrUnlockRejectOutMessage inner =>
    simp only [encode, UserAddrUnlockRejectOutMessage.encode_length]
    omega
  | branchOrdValLimitUpdateOuMessage inner =>
    simp only [encode, BranchOrdValLimitUpdateOuMessage.encode_length]
    omega
  | userOrderLimitUpdateOutMessage inner =>
    simp only [encode, UserOrderLimitUpdateOutMessage.encode_length]
    omega
  | dealerLimitUpdateOutMessage inner =>
    simp only [encode, DealerLimitUpdateOutMessage.encode_length]
    omega
  | resetUserPasswordOutMessage inner =>
    simp only [encode, ResetUserPasswordOutMessage.encode_length]
    omega
  | colUserStatusChangeOutMessage inner =>
    simp only [encode, ColUserStatusChangeOutMessage.encode_length]
    omega
  | spdOrdLimitUpdateOutMessage inner =>
    simp only [encode, SpdOrdLimitUpdateOutMessage.encode_length]
    omega
  | headerRecordMessage inner =>
    simp only [encode, HeaderRecordMessage.encode_length]
    omega
  | messageRecordMessage inner =>
    simp only [encode, MessageRecordMessage.encode_length]
    omega
  | trailerRecordMessage inner =>
    simp only [encode, TrailerRecordMessage.encode_length]
    omega
  | updateLocaldbHeaderMessage inner =>
    simp only [encode, UpdateLocaldbHeaderMessage.encode_length]
    omega
  | updateLocaldbTrailerMessage inner =>
    simp only [encode, UpdateLocaldbTrailerMessage.encode_length]
    omega
  | bcastAssetMstrChgMessage inner =>
    simp only [encode, BcastAssetMstrChgMessage.encode_length]
    omega
  | boxSignOnRequestOutMessage inner =>
    simp only [encode, BoxSignOnRequestOutMessage.encode_length]
    omega
  | secureBoxRegistrationResponseOutMessage inner =>
    simp only [encode, SecureBoxRegistrationResponseOutMessage.encode_length]
    omega
  | boxSignOffMessage inner =>
    simp only [encode, BoxSignOffMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessagePayload × List UInt8) :=
  if tag = 1601 then (SystemInformationOutMessage.decode bytes).map fun (message, rest) => (.systemInformationOutMessage message, rest)
  else if tag = 7321 then (PartialSystemInformationMessage.decode bytes).map fun (message, rest) => (.partialSystemInformationMessage message, rest)
  else if tag = 1821 then (OpenOrderReportMessage.decode bytes).map fun (message, rest) => (.openOrderReportMessage message, rest)
  else if tag = 1992 then (SpreadOrderLogReportMessage.decode bytes).map fun (message, rest) => (.spreadOrderLogReportMessage message, rest)
  else if tag = 1993 then (SpreadTradeReportMessage.decode bytes).map fun (message, rest) => (.spreadTradeReportMessage message, rest)
  else if tag = 2001 then (BoardLotOutMessage.decode bytes).map fun (message, rest) => (.boardLotOutMessage message, rest)
  else if tag = 2008 then (NegOrderToBlMessage.decode bytes).map fun (message, rest) => (.negOrderToBlMessage message, rest)
  else if tag = 2041 then (OrderModOutMessage.decode bytes).map fun (message, rest) => (.orderModOutMessage message, rest)
  else if tag = 2042 then (OrderModRejectMessage.decode bytes).map fun (message, rest) => (.orderModRejectMessage message, rest)
  else if tag = 2071 then (OrderCancelOutMessage.decode bytes).map fun (message, rest) => (.orderCancelOutMessage message, rest)
  else if tag = 2072 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 2073 then (OrderConfirmationMessage.decode bytes).map fun (message, rest) => (.orderConfirmationMessage message, rest)
  else if tag = 2074 then (OrderModConfirmationMessage.decode bytes).map fun (message, rest) => (.orderModConfirmationMessage message, rest)
  else if tag = 2075 then (OrderCancelConfirmationMessage.decode bytes).map fun (message, rest) => (.orderCancelConfirmationMessage message, rest)
  else if tag = 2076 then (CancelNegOrderMessage.decode bytes).map fun (message, rest) => (.cancelNegOrderMessage message, rest)
  else if tag = 2170 then (FreezeToControlMessage.decode bytes).map fun (message, rest) => (.freezeToControlMessage message, rest)
  else if tag = 2231 then (OrderErrorMessage.decode bytes).map fun (message, rest) => (.orderErrorMessage message, rest)
  else if tag = 9002 then (BatchOrderCancelMessage.decode bytes).map fun (message, rest) => (.batchOrderCancelMessage message, rest)
  else if tag = 2101 then (SpBoardLotOutMessage.decode bytes).map fun (message, rest) => (.spBoardLotOutMessage message, rest)
  else if tag = 2103 then (TwolBoardLotOutMessage.decode bytes).map fun (message, rest) => (.twolBoardLotOutMessage message, rest)
  else if tag = 2105 then (ThrlBoardLotOutMessage.decode bytes).map fun (message, rest) => (.thrlBoardLotOutMessage message, rest)
  else if tag = 2107 then (SpOrderCancelOutMessage.decode bytes).map fun (message, rest) => (.spOrderCancelOutMessage message, rest)
  else if tag = 2119 then (SpOrderModOutMessage.decode bytes).map fun (message, rest) => (.spOrderModOutMessage message, rest)
  else if tag = 2124 then (SpOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.spOrderConfirmationMessage message, rest)
  else if tag = 2125 then (TwolOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.twolOrderConfirmationMessage message, rest)
  else if tag = 2126 then (ThrlOrderConfirmationMessage.decode bytes).map fun (message, rest) => (.thrlOrderConfirmationMessage message, rest)
  else if tag = 2127 then (SpOrderCxlRejOutMessage.decode bytes).map fun (message, rest) => (.spOrderCxlRejOutMessage message, rest)
  else if tag = 2130 then (SpOrderCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.spOrderCxlConfirmationMessage message, rest)
  else if tag = 2131 then (TwolOrderCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.twolOrderCxlConfirmationMessage message, rest)
  else if tag = 2132 then (ThrlOrderCxlConfirmationMessage.decode bytes).map fun (message, rest) => (.thrlOrderCxlConfirmationMessage message, rest)
  else if tag = 2133 then (SpOrderModRejOutMessage.decode bytes).map fun (message, rest) => (.spOrderModRejOutMessage message, rest)
  else if tag = 2136 then (SpOrderModConOutMessage.decode bytes).map fun (message, rest) => (.spOrderModConOutMessage message, rest)
  else if tag = 2155 then (TwolOrderErrorMessage.decode bytes).map fun (message, rest) => (.twolOrderErrorMessage message, rest)
  else if tag = 2156 then (ThrlOrderErrorMessage.decode bytes).map fun (message, rest) => (.thrlOrderErrorMessage message, rest)
  else if tag = 2212 then (OnStopNotificationMessage.decode bytes).map fun (message, rest) => (.onStopNotificationMessage message, rest)
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).map fun (message, rest) => (.tradeConfirmationMessage message, rest)
  else if tag = 2282 then (TradeCancelConfirmMessage.decode bytes).map fun (message, rest) => (.tradeCancelConfirmMessage message, rest)
  else if tag = 2286 then (TradeCancelRejectMessage.decode bytes).map fun (message, rest) => (.tradeCancelRejectMessage message, rest)
  else if tag = 2288 then (TradeModifyRejectMessage.decode bytes).map fun (message, rest) => (.tradeModifyRejectMessage message, rest)
  else if tag = 2223 then (TradeErrorMessage.decode bytes).map fun (message, rest) => (.tradeErrorMessage message, rest)
  else if tag = 5441 then (TradeCancelOutMessage.decode bytes).map fun (message, rest) => (.tradeCancelOutMessage message, rest)
  else if tag = 2287 then (TradeModifyConfirmMessage.decode bytes).map fun (message, rest) => (.tradeModifyConfirmMessage message, rest)
  else if tag = 2301 then (SignOnRequestOutMessage.decode bytes).map fun (message, rest) => (.signOnRequestOutMessage message, rest)
  else if tag = 5585 then (SignOffTraderOutMessage.decode bytes).map fun (message, rest) => (.signOffTraderOutMessage message, rest)
  else if tag = 2302 then (ErrorResponseOutMessage.decode bytes).map fun (message, rest) => (.errorResponseOutMessage message, rest)
  else if tag = 2401 then (GrResponseMessage.decode bytes).map fun (message, rest) => (.grResponseMessage message, rest)
  else if tag = 5428 then (UserAddrUnlockConfirmOutMessage.decode bytes).map fun (message, rest) => (.userAddrUnlockConfirmOutMessage message, rest)
  else if tag = 5483 then (UserAddrUnlockApproveOutMessage.decode bytes).map fun (message, rest) => (.userAddrUnlockApproveOutMessage message, rest)
  else if tag = 5484 then (UserAddrUnlockRejectOutMessage.decode bytes).map fun (message, rest) => (.userAddrUnlockRejectOutMessage message, rest)
  else if tag = 5717 then (BranchOrdValLimitUpdateOuMessage.decode bytes).map fun (message, rest) => (.branchOrdValLimitUpdateOuMessage message, rest)
  else if tag = 5731 then (UserOrderLimitUpdateOutMessage.decode bytes).map fun (message, rest) => (.userOrderLimitUpdateOutMessage message, rest)
  else if tag = 5733 then (DealerLimitUpdateOutMessage.decode bytes).map fun (message, rest) => (.dealerLimitUpdateOutMessage message, rest)
  else if tag = 5741 then (ResetUserPasswordOutMessage.decode bytes).map fun (message, rest) => (.resetUserPasswordOutMessage message, rest)
  else if tag = 5745 then (ColUserStatusChangeOutMessage.decode bytes).map fun (message, rest) => (.colUserStatusChangeOutMessage message, rest)
  else if tag = 5772 then (SpdOrdLimitUpdateOutMessage.decode bytes).map fun (message, rest) => (.spdOrdLimitUpdateOutMessage message, rest)
  else if tag = 7011 then (HeaderRecordMessage.decode bytes).map fun (message, rest) => (.headerRecordMessage message, rest)
  else if tag = 7021 then (MessageRecordMessage.decode bytes).map fun (message, rest) => (.messageRecordMessage message, rest)
  else if tag = 7031 then (TrailerRecordMessage.decode bytes).map fun (message, rest) => (.trailerRecordMessage message, rest)
  else if tag = 7307 then (UpdateLocaldbHeaderMessage.decode bytes).map fun (message, rest) => (.updateLocaldbHeaderMessage message, rest)
  else if tag = 7308 then (UpdateLocaldbTrailerMessage.decode bytes).map fun (message, rest) => (.updateLocaldbTrailerMessage message, rest)
  else if tag = 7325 then (BcastAssetMstrChgMessage.decode bytes).map fun (message, rest) => (.bcastAssetMstrChgMessage message, rest)
  else if tag = 23001 then (BoxSignOnRequestOutMessage.decode bytes).map fun (message, rest) => (.boxSignOnRequestOutMessage message, rest)
  else if tag = 23009 then (SecureBoxRegistrationResponseOutMessage.decode bytes).map fun (message, rest) => (.secureBoxRegistrationResponseOutMessage message, rest)
  else if tag = 20322 then (BoxSignOffMessage.decode bytes).map fun (message, rest) => (.boxSignOffMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessagePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessagePayload

/-- Server Message -/
structure ServerMessage where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  serverMessagePayload : ServerMessagePayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encodeBody (message : ServerMessage) : List UInt8 :=
  ServerMessagePayload.encode message.serverMessagePayload

def decodeBody (transactionCode : BitVec 16) (logTime : BitVec 32) (alphaChar : Alpha 2) (traderId : BitVec 32) (errorCode : BitVec 16) (headerTimestamp : BitVec 64) (timeStamp1 : Alpha 8) (timeStamp2 : Alpha 8) (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (serverMessagePayload, bytes) ← ServerMessagePayload.decode transactionCode bytes
  pure ({ logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, serverMessagePayload }, bytes)

theorem decodeBody_encodeBody (message : ServerMessage) (rest : List UInt8) :
    decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2 (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [ServerMessagePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerMessage) : (encodeBody message).length + 40 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverMessagePayload with
  | systemInformationOutMessage inner =>
    simp only [ServerMessagePayload.encode, SystemInformationOutMessage.encode_length]
    omega
  | partialSystemInformationMessage inner =>
    simp only [ServerMessagePayload.encode, PartialSystemInformationMessage.encode_length]
    omega
  | openOrderReportMessage inner =>
    simp only [ServerMessagePayload.encode, OpenOrderReportMessage.encode_length]
    omega
  | spreadOrderLogReportMessage inner =>
    simp only [ServerMessagePayload.encode, SpreadOrderLogReportMessage.encode_length]
    omega
  | spreadTradeReportMessage inner =>
    simp only [ServerMessagePayload.encode, SpreadTradeReportMessage.encode_length]
    omega
  | boardLotOutMessage inner =>
    simp only [ServerMessagePayload.encode, BoardLotOutMessage.encode_length]
    omega
  | negOrderToBlMessage inner =>
    simp only [ServerMessagePayload.encode, NegOrderToBlMessage.encode_length]
    omega
  | orderModOutMessage inner =>
    simp only [ServerMessagePayload.encode, OrderModOutMessage.encode_length]
    omega
  | orderModRejectMessage inner =>
    simp only [ServerMessagePayload.encode, OrderModRejectMessage.encode_length]
    omega
  | orderCancelOutMessage inner =>
    simp only [ServerMessagePayload.encode, OrderCancelOutMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderConfirmationMessage.encode_length]
    omega
  | orderModConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderModConfirmationMessage.encode_length]
    omega
  | orderCancelConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, OrderCancelConfirmationMessage.encode_length]
    omega
  | cancelNegOrderMessage inner =>
    simp only [ServerMessagePayload.encode, CancelNegOrderMessage.encode_length]
    omega
  | freezeToControlMessage inner =>
    simp only [ServerMessagePayload.encode, FreezeToControlMessage.encode_length]
    omega
  | orderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, OrderErrorMessage.encode_length]
    omega
  | batchOrderCancelMessage inner =>
    simp only [ServerMessagePayload.encode, BatchOrderCancelMessage.encode_length]
    omega
  | spBoardLotOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpBoardLotOutMessage.encode_length]
    omega
  | twolBoardLotOutMessage inner =>
    simp only [ServerMessagePayload.encode, TwolBoardLotOutMessage.encode_length]
    omega
  | thrlBoardLotOutMessage inner =>
    simp only [ServerMessagePayload.encode, ThrlBoardLotOutMessage.encode_length]
    omega
  | spOrderCancelOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderCancelOutMessage.encode_length]
    omega
  | spOrderModOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderModOutMessage.encode_length]
    omega
  | spOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderConfirmationMessage.encode_length]
    omega
  | twolOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, TwolOrderConfirmationMessage.encode_length]
    omega
  | thrlOrderConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, ThrlOrderConfirmationMessage.encode_length]
    omega
  | spOrderCxlRejOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderCxlRejOutMessage.encode_length]
    omega
  | spOrderCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderCxlConfirmationMessage.encode_length]
    omega
  | twolOrderCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, TwolOrderCxlConfirmationMessage.encode_length]
    omega
  | thrlOrderCxlConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, ThrlOrderCxlConfirmationMessage.encode_length]
    omega
  | spOrderModRejOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderModRejOutMessage.encode_length]
    omega
  | spOrderModConOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpOrderModConOutMessage.encode_length]
    omega
  | twolOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, TwolOrderErrorMessage.encode_length]
    omega
  | thrlOrderErrorMessage inner =>
    simp only [ServerMessagePayload.encode, ThrlOrderErrorMessage.encode_length]
    omega
  | onStopNotificationMessage inner =>
    simp only [ServerMessagePayload.encode, OnStopNotificationMessage.encode_length]
    omega
  | tradeConfirmationMessage inner =>
    simp only [ServerMessagePayload.encode, TradeConfirmationMessage.encode_length]
    omega
  | tradeCancelConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, TradeCancelConfirmMessage.encode_length]
    omega
  | tradeCancelRejectMessage inner =>
    simp only [ServerMessagePayload.encode, TradeCancelRejectMessage.encode_length]
    omega
  | tradeModifyRejectMessage inner =>
    simp only [ServerMessagePayload.encode, TradeModifyRejectMessage.encode_length]
    omega
  | tradeErrorMessage inner =>
    simp only [ServerMessagePayload.encode, TradeErrorMessage.encode_length]
    omega
  | tradeCancelOutMessage inner =>
    simp only [ServerMessagePayload.encode, TradeCancelOutMessage.encode_length]
    omega
  | tradeModifyConfirmMessage inner =>
    simp only [ServerMessagePayload.encode, TradeModifyConfirmMessage.encode_length]
    omega
  | signOnRequestOutMessage inner =>
    simp only [ServerMessagePayload.encode, SignOnRequestOutMessage.encode_length]
    omega
  | signOffTraderOutMessage inner =>
    simp only [ServerMessagePayload.encode, SignOffTraderOutMessage.encode_length]
    omega
  | errorResponseOutMessage inner =>
    simp only [ServerMessagePayload.encode, ErrorResponseOutMessage.encode_length]
    omega
  | grResponseMessage inner =>
    simp only [ServerMessagePayload.encode, GrResponseMessage.encode_length]
    omega
  | userAddrUnlockConfirmOutMessage inner =>
    simp only [ServerMessagePayload.encode, UserAddrUnlockConfirmOutMessage.encode_length]
    omega
  | userAddrUnlockApproveOutMessage inner =>
    simp only [ServerMessagePayload.encode, UserAddrUnlockApproveOutMessage.encode_length]
    omega
  | userAddrUnlockRejectOutMessage inner =>
    simp only [ServerMessagePayload.encode, UserAddrUnlockRejectOutMessage.encode_length]
    omega
  | branchOrdValLimitUpdateOuMessage inner =>
    simp only [ServerMessagePayload.encode, BranchOrdValLimitUpdateOuMessage.encode_length]
    omega
  | userOrderLimitUpdateOutMessage inner =>
    simp only [ServerMessagePayload.encode, UserOrderLimitUpdateOutMessage.encode_length]
    omega
  | dealerLimitUpdateOutMessage inner =>
    simp only [ServerMessagePayload.encode, DealerLimitUpdateOutMessage.encode_length]
    omega
  | resetUserPasswordOutMessage inner =>
    simp only [ServerMessagePayload.encode, ResetUserPasswordOutMessage.encode_length]
    omega
  | colUserStatusChangeOutMessage inner =>
    simp only [ServerMessagePayload.encode, ColUserStatusChangeOutMessage.encode_length]
    omega
  | spdOrdLimitUpdateOutMessage inner =>
    simp only [ServerMessagePayload.encode, SpdOrdLimitUpdateOutMessage.encode_length]
    omega
  | headerRecordMessage inner =>
    simp only [ServerMessagePayload.encode, HeaderRecordMessage.encode_length]
    omega
  | messageRecordMessage inner =>
    simp only [ServerMessagePayload.encode, MessageRecordMessage.encode_length]
    omega
  | trailerRecordMessage inner =>
    simp only [ServerMessagePayload.encode, TrailerRecordMessage.encode_length]
    omega
  | updateLocaldbHeaderMessage inner =>
    simp only [ServerMessagePayload.encode, UpdateLocaldbHeaderMessage.encode_length]
    omega
  | updateLocaldbTrailerMessage inner =>
    simp only [ServerMessagePayload.encode, UpdateLocaldbTrailerMessage.encode_length]
    omega
  | bcastAssetMstrChgMessage inner =>
    simp only [ServerMessagePayload.encode, BcastAssetMstrChgMessage.encode_length]
    omega
  | boxSignOnRequestOutMessage inner =>
    simp only [ServerMessagePayload.encode, BoxSignOnRequestOutMessage.encode_length]
    omega
  | secureBoxRegistrationResponseOutMessage inner =>
    simp only [ServerMessagePayload.encode, SecureBoxRegistrationResponseOutMessage.encode_length]
    omega
  | boxSignOffMessage inner =>
    simp only [ServerMessagePayload.encode, BoxSignOffMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 40, so it is written from the body and checked on decode; Transaction Code, Log Time, Alpha Char, Trader Id, Error Code, Header Timestamp, Time Stamp 1, Time Stamp 2 are read ahead of it -/
def encode (message : ServerMessage) : List UInt8 :=
  encodeUInt 2 (ServerMessagePayload.tag message.serverMessagePayload)
    ++ (encodeUInt 4 message.logTime
    ++ (Alpha.encode message.alphaChar
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.errorCode
    ++ (encodeUInt 8 message.headerTimestamp
    ++ (Alpha.encode message.timeStamp1
    ++ (Alpha.encode message.timeStamp2
    ++ (encodeFramed 2 40 encodeBody message))))))))

def decode (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  decodeFramed 2 40 (decodeBody transactionCode logTime alphaChar traderId errorCode headerTimestamp timeStamp1 timeStamp2) bytes

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 2 40 encodeBody (decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end ServerPacket

end Omi.NseNsecomOrderentryNnfV35Server
