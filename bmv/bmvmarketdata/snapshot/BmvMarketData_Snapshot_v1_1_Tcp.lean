import Wire

/-!
# Bolsa Mexicana de Valores Bmv Market Data Snapshot v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no
bound the prefix must fit; the body is read by its content

License: MIT No Attribution
-/

namespace Omi.BmvBmvmarketdataSnapshotIntraV11Tcp

/-- Login Response Status: one byte code -/
def LoginResponseStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44]

inductive LoginResponseStatus where
  | acceptedSession -- Accepted Session
  | invalidMarketDataGroup -- Invalid Market Data Group
  | loginOnAnotherChannel -- Login On Another Channel
  | unavailableService -- Unavailable Service
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginResponseStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginResponseStatus

def toByte : LoginResponseStatus → UInt8
  | .acceptedSession => 0x41
  | .invalidMarketDataGroup => 0x42
  | .loginOnAnotherChannel => 0x43
  | .unavailableService => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginResponseStatus :=
  if byte = 0x41 then .acceptedSession
  else if byte = 0x42 then .invalidMarketDataGroup
  else if byte = 0x43 then .loginOnAnotherChannel
  else .unavailableService

def ofByte (byte : UInt8) : LoginResponseStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginResponseStatus) : ofByte value.toByte = value := by
  cases value with
  | acceptedSession => decide
  | invalidMarketDataGroup => decide
  | loginOnAnotherChannel => decide
  | unavailableService => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginResponseStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginResponseStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginResponseStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LoginResponseStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LoginResponseStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginResponseStatus

/-- Replay Response Status: one byte code -/
def ReplayResponseStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x45, 0x46, 0x47, 0x4A, 0x4B]

inductive ReplayResponseStatus where
  | acceptedRequest -- Accepted Request
  | invalidMarketDataGroup -- Invalid Market Data Group
  | unavailableService -- Unavailable Service
  | notLoggedIn -- Not Logged In
  | surpassRequestsLimit -- Surpass Requests Limit
  | outOfRange -- Out Of Range
  | firstInvalidMessage -- First Invalid Message
  | invalidQuantity -- Invalid Quantity
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayResponseStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayResponseStatus

def toByte : ReplayResponseStatus → UInt8
  | .acceptedRequest => 0x41
  | .invalidMarketDataGroup => 0x42
  | .unavailableService => 0x44
  | .notLoggedIn => 0x45
  | .surpassRequestsLimit => 0x46
  | .outOfRange => 0x47
  | .firstInvalidMessage => 0x4A
  | .invalidQuantity => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayResponseStatus :=
  if byte = 0x41 then .acceptedRequest
  else if byte = 0x42 then .invalidMarketDataGroup
  else if byte = 0x44 then .unavailableService
  else if byte = 0x45 then .notLoggedIn
  else if byte = 0x46 then .surpassRequestsLimit
  else if byte = 0x47 then .outOfRange
  else if byte = 0x4A then .firstInvalidMessage
  else .invalidQuantity

def ofByte (byte : UInt8) : ReplayResponseStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayResponseStatus) : ofByte value.toByte = value := by
  cases value with
  | acceptedRequest => decide
  | invalidMarketDataGroup => decide
  | unavailableService => decide
  | notLoggedIn => decide
  | surpassRequestsLimit => decide
  | outOfRange => decide
  | firstInvalidMessage => decide
  | invalidQuantity => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReplayResponseStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReplayResponseStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReplayResponseStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReplayResponseStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReplayResponseStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReplayResponseStatus

/-- Snapshot Response Status: one byte code -/
def SnapshotResponseStatus.codes : List UInt8 :=
  [0x41, 0x42, 0x44, 0x45, 0x46, 0x48, 0x49, 0x4C, 0x4D, 0x53]

inductive SnapshotResponseStatus where
  | acceptedRequest -- Accepted Request
  | invalidMarketDataGroup -- Invalid Market Data Group
  | unavailableService -- Unavailable Service
  | notLoggedIn -- Not Logged In
  | surpassRequestsLimit -- Surpass Requests Limit
  | invalidSnapshotType -- Invalid Snapshot Type
  | invalidIdentifierInstrument -- Invalid Identifier Instrument
  | marketDataCombinationUnavailableSnapshotType -- Market Data Combination Unavailable Snapshot Type
  | emptyInformationFromRequestedInstrument -- Empty Information From Requested Instrument
  | invalidSample -- Invalid Sample
  | unlisted (byte : { byte : UInt8 // byte ∉ SnapshotResponseStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SnapshotResponseStatus

def toByte : SnapshotResponseStatus → UInt8
  | .acceptedRequest => 0x41
  | .invalidMarketDataGroup => 0x42
  | .unavailableService => 0x44
  | .notLoggedIn => 0x45
  | .surpassRequestsLimit => 0x46
  | .invalidSnapshotType => 0x48
  | .invalidIdentifierInstrument => 0x49
  | .marketDataCombinationUnavailableSnapshotType => 0x4C
  | .emptyInformationFromRequestedInstrument => 0x4D
  | .invalidSample => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SnapshotResponseStatus :=
  if byte = 0x41 then .acceptedRequest
  else if byte = 0x42 then .invalidMarketDataGroup
  else if byte = 0x44 then .unavailableService
  else if byte = 0x45 then .notLoggedIn
  else if byte = 0x46 then .surpassRequestsLimit
  else if byte = 0x48 then .invalidSnapshotType
  else if byte = 0x49 then .invalidIdentifierInstrument
  else if byte = 0x4C then .marketDataCombinationUnavailableSnapshotType
  else if byte = 0x4D then .emptyInformationFromRequestedInstrument
  else .invalidSample

def ofByte (byte : UInt8) : SnapshotResponseStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SnapshotResponseStatus) : ofByte value.toByte = value := by
  cases value with
  | acceptedRequest => decide
  | invalidMarketDataGroup => decide
  | unavailableService => decide
  | notLoggedIn => decide
  | surpassRequestsLimit => decide
  | invalidSnapshotType => decide
  | invalidIdentifierInstrument => decide
  | marketDataCombinationUnavailableSnapshotType => decide
  | emptyInformationFromRequestedInstrument => decide
  | invalidSample => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SnapshotResponseStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SnapshotResponseStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SnapshotResponseStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SnapshotResponseStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SnapshotResponseStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SnapshotResponseStatus

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

/-- Instrument Status: one byte code -/
def InstrumentStatus.codes : List UInt8 :=
  [0x43, 0x41, 0x50, 0x45, 0x47, 0x54, 0x4E, 0x4B, 0x4D, 0x55, 0x4F, 0x56, 0x4C, 0x49, 0x42, 0x57, 0x58, 0x59, 0x52]

inductive InstrumentStatus where
  | cancellationOfOffers -- Cancellation Of Offers
  | openingAuction -- Opening Auction
  | preOpening -- Pre Opening
  | beingAllocated -- Being Allocated
  | auctionAllocated -- Auction Allocated
  | auctionEnded -- Auction Ended
  | continuousTrading -- Continuous Trading
  | breakingAuctionParameters -- Breaking Auction Parameters
  | continuousAuctionDueToStopOperatingMoreThan20WorkingDays -- Continuous Auction Due To Stop Operating More Than 20 Working Days
  | cleavingAuction -- Cleaving Auction
  | suspendedSeries -- Suspended Series
  | suspendedQuotation -- Suspended Quotation
  | auctionForBreach -- Auction For Breach
  | withdrawalOfOrdersOnContinuousAuction -- Withdrawal Of Orders On Continuous Auction
  | withdrawalOfOrderOnIntradayAuction -- Withdrawal Of Order On Intraday Auction
  | newsPending -- News Pending
  | settlementAuction -- Settlement Auction
  | extraordinarySettlementAuction -- Extraordinary Settlement Auction
  | auctionTotalOfCkDes -- Auction Total Of Ck Des
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentStatus

def toByte : InstrumentStatus → UInt8
  | .cancellationOfOffers => 0x43
  | .openingAuction => 0x41
  | .preOpening => 0x50
  | .beingAllocated => 0x45
  | .auctionAllocated => 0x47
  | .auctionEnded => 0x54
  | .continuousTrading => 0x4E
  | .breakingAuctionParameters => 0x4B
  | .continuousAuctionDueToStopOperatingMoreThan20WorkingDays => 0x4D
  | .cleavingAuction => 0x55
  | .suspendedSeries => 0x4F
  | .suspendedQuotation => 0x56
  | .auctionForBreach => 0x4C
  | .withdrawalOfOrdersOnContinuousAuction => 0x49
  | .withdrawalOfOrderOnIntradayAuction => 0x42
  | .newsPending => 0x57
  | .settlementAuction => 0x58
  | .extraordinarySettlementAuction => 0x59
  | .auctionTotalOfCkDes => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentStatus :=
  if byte = 0x43 then .cancellationOfOffers
  else if byte = 0x41 then .openingAuction
  else if byte = 0x50 then .preOpening
  else if byte = 0x45 then .beingAllocated
  else if byte = 0x47 then .auctionAllocated
  else if byte = 0x54 then .auctionEnded
  else if byte = 0x4E then .continuousTrading
  else if byte = 0x4B then .breakingAuctionParameters
  else if byte = 0x4D then .continuousAuctionDueToStopOperatingMoreThan20WorkingDays
  else if byte = 0x55 then .cleavingAuction
  else if byte = 0x4F then .suspendedSeries
  else if byte = 0x56 then .suspendedQuotation
  else if byte = 0x4C then .auctionForBreach
  else if byte = 0x49 then .withdrawalOfOrdersOnContinuousAuction
  else if byte = 0x42 then .withdrawalOfOrderOnIntradayAuction
  else if byte = 0x57 then .newsPending
  else if byte = 0x58 then .settlementAuction
  else if byte = 0x59 then .extraordinarySettlementAuction
  else .auctionTotalOfCkDes

def ofByte (byte : UInt8) : InstrumentStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentStatus) : ofByte value.toByte = value := by
  cases value with
  | cancellationOfOffers => decide
  | openingAuction => decide
  | preOpening => decide
  | beingAllocated => decide
  | auctionAllocated => decide
  | auctionEnded => decide
  | continuousTrading => decide
  | breakingAuctionParameters => decide
  | continuousAuctionDueToStopOperatingMoreThan20WorkingDays => decide
  | cleavingAuction => decide
  | suspendedSeries => decide
  | suspendedQuotation => decide
  | auctionForBreach => decide
  | withdrawalOfOrdersOnContinuousAuction => decide
  | withdrawalOfOrderOnIntradayAuction => decide
  | newsPending => decide
  | settlementAuction => decide
  | extraordinarySettlementAuction => decide
  | auctionTotalOfCkDes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : InstrumentStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : InstrumentStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentStatus

/-- Concertation Type: one byte code -/
def ConcertationType.codes : List UInt8 :=
  [0x43, 0x4F, 0x48, 0x44, 0x4D, 0x50, 0x58, 0x76, 0x77, 0x25, 0x78, 0x79, 0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B, 0x4C, 0x4E, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x7A, 0x23, 0x49, 0x2B, 0x26, 0x28, 0x29]

inductive ConcertationType where
  | crossingOperation -- Crossing Operation
  | orderClosing -- Order Closing
  | operationAtClosingPrice -- Operation At Closing Price
  | operationAfterClosing -- Operation After Closing
  | operationAtMediumPrice -- Operation At Medium Price
  | operationAtAveragePriceForTheDay -- Operation At Average Price For The Day
  | blockOperationsByException -- Block Operations By Exception
  | vwapOperationsByException -- Vwap Operations By Exception
  | twapOperationsByException -- Twap Operations By Exception
  | basketTrading -- Basket Trading
  | otcRecentOperations -- Otc Recent Operations
  | otcAgreedOperations -- Otc Agreed Operations
  | buyAutoEntry -- Buy Auto Entry
  | sellAutoEntry -- Sell Auto Entry
  | blockTrade -- Block Trade
  | legOfBlocktradeForChainOfForwards -- Leg Of Blocktrade For Chain Of Forwards
  | legOfChainOfForwards -- Leg Of Chain Of Forwards
  | legOfCrossingOfForeignCurrencyStrategy -- Leg Of Crossing Of Foreign Currency Strategy
  | sellLegAutoEntryOfForeignCurrencyStrategy -- Sell Leg Auto Entry Of Foreign Currency Strategy
  | buyLegAutoEntryOfForeignCurrencyStrategy -- Buy Leg Auto Entry Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy -- Leg Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy_51 -- Leg Of Foreign Currency Strategy
  | legOfCrossingOfChainOfForwards -- Leg Of Crossing Of Chain Of Forwards
  | sellLegAutoEntryOfChainOfForwards -- Sell Leg Auto Entry Of Chain Of Forwards
  | buyLegAutoEntryOfChainOfForwards -- Buy Leg Auto Entry Of Chain Of Forwards
  | legOfAuctionOfChainOfForwards -- Leg Of Auction Of Chain Of Forwards
  | legOfRoundOfChainOfForwards -- Leg Of Round Of Chain Of Forwards
  | chainsOfForwards -- Chains Of Forwards
  | legOfRolloverCrossing -- Leg Of Rollover Crossing
  | sellLegAutoEntryOfRollover -- Sell Leg Auto Entry Of Rollover
  | buyLegAutoEntryOfRollover -- Buy Leg Auto Entry Of Rollover
  | legOfRoundOfRollover -- Leg Of Round Of Rollover
  | depthOfRoundOfChainOfForwards -- Depth Of Round Of Chain Of Forwards
  | tradingOfChainOfForwards -- Trading Of Chain Of Forwards
  | depthOfRound -- Depth Of Round
  | roundOfChainOfForwards -- Round Of Chain Of Forwards
  | rolloverSentra -- Rollover Sentra
  | typeRound -- Type Round
  | auctions -- Auctions
  | legOfBlockTradeOfRollover -- Leg Of Block Trade Of Rollover
  | legOfBlockTradeOfForeignCurrencyStrategy -- Leg Of Block Trade Of Foreign Currency Strategy
  | blockTradeOfForeignCurrencyStrategy -- Block Trade Of Foreign Currency Strategy
  | blockTradeOfChainOfForwards -- Block Trade Of Chain Of Forwards
  | blocktradeOfRollover -- Blocktrade Of Rollover
  | crossingOfChainOfForwards -- Crossing Of Chain Of Forwards
  | sellAutoEntryOfChainOfForwards -- Sell Auto Entry Of Chain Of Forwards
  | buyAutoEntryOfChainOfForwards -- Buy Auto Entry Of Chain Of Forwards
  | swapBlockTrade -- Swap Block Trade
  | swapBlockTradeWithContinuousCoupon -- Swap Block Trade With Continuous Coupon
  | blockTradeOfUnwind -- Block Trade Of Unwind
  | blockTradeOfSubstitution -- Block Trade Of Substitution
  | voiceOver -- Voice Over
  | firmOrder -- Firm Order
  | ipoCross -- Ipo Cross
  | unintentionalSelfCross -- Unintentional Self Cross
  | withoutConcertation -- Without Concertation
  | inavToClosingPriceTrading -- Inav To Closing Price Trading
  | inavAfterClosing -- Inav After Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ ConcertationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ConcertationType

def toByte : ConcertationType → UInt8
  | .crossingOperation => 0x43
  | .orderClosing => 0x4F
  | .operationAtClosingPrice => 0x48
  | .operationAfterClosing => 0x44
  | .operationAtMediumPrice => 0x4D
  | .operationAtAveragePriceForTheDay => 0x50
  | .blockOperationsByException => 0x58
  | .vwapOperationsByException => 0x76
  | .twapOperationsByException => 0x77
  | .basketTrading => 0x25
  | .otcRecentOperations => 0x78
  | .otcAgreedOperations => 0x79
  | .buyAutoEntry => 0x41
  | .sellAutoEntry => 0x42
  | .blockTrade => 0x45
  | .legOfBlocktradeForChainOfForwards => 0x46
  | .legOfChainOfForwards => 0x47
  | .legOfCrossingOfForeignCurrencyStrategy => 0x4A
  | .sellLegAutoEntryOfForeignCurrencyStrategy => 0x4B
  | .buyLegAutoEntryOfForeignCurrencyStrategy => 0x4C
  | .legOfForeignCurrencyStrategy => 0x4E
  | .legOfForeignCurrencyStrategy_51 => 0x51
  | .legOfCrossingOfChainOfForwards => 0x52
  | .sellLegAutoEntryOfChainOfForwards => 0x53
  | .buyLegAutoEntryOfChainOfForwards => 0x54
  | .legOfAuctionOfChainOfForwards => 0x55
  | .legOfRoundOfChainOfForwards => 0x56
  | .chainsOfForwards => 0x57
  | .legOfRolloverCrossing => 0x59
  | .sellLegAutoEntryOfRollover => 0x5A
  | .buyLegAutoEntryOfRollover => 0x61
  | .legOfRoundOfRollover => 0x62
  | .depthOfRoundOfChainOfForwards => 0x63
  | .tradingOfChainOfForwards => 0x64
  | .depthOfRound => 0x65
  | .roundOfChainOfForwards => 0x66
  | .rolloverSentra => 0x67
  | .typeRound => 0x68
  | .auctions => 0x69
  | .legOfBlockTradeOfRollover => 0x6A
  | .legOfBlockTradeOfForeignCurrencyStrategy => 0x6B
  | .blockTradeOfForeignCurrencyStrategy => 0x6C
  | .blockTradeOfChainOfForwards => 0x6D
  | .blocktradeOfRollover => 0x6E
  | .crossingOfChainOfForwards => 0x6F
  | .sellAutoEntryOfChainOfForwards => 0x70
  | .buyAutoEntryOfChainOfForwards => 0x71
  | .swapBlockTrade => 0x72
  | .swapBlockTradeWithContinuousCoupon => 0x73
  | .blockTradeOfUnwind => 0x74
  | .blockTradeOfSubstitution => 0x75
  | .voiceOver => 0x7A
  | .firmOrder => 0x23
  | .ipoCross => 0x49
  | .unintentionalSelfCross => 0x2B
  | .withoutConcertation => 0x26
  | .inavToClosingPriceTrading => 0x28
  | .inavAfterClosing => 0x29
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ConcertationType :=
  if byte = 0x43 then .crossingOperation
  else if byte = 0x4F then .orderClosing
  else if byte = 0x48 then .operationAtClosingPrice
  else if byte = 0x44 then .operationAfterClosing
  else if byte = 0x4D then .operationAtMediumPrice
  else if byte = 0x50 then .operationAtAveragePriceForTheDay
  else if byte = 0x58 then .blockOperationsByException
  else if byte = 0x76 then .vwapOperationsByException
  else if byte = 0x77 then .twapOperationsByException
  else if byte = 0x25 then .basketTrading
  else if byte = 0x78 then .otcRecentOperations
  else if byte = 0x79 then .otcAgreedOperations
  else if byte = 0x41 then .buyAutoEntry
  else if byte = 0x42 then .sellAutoEntry
  else if byte = 0x45 then .blockTrade
  else if byte = 0x46 then .legOfBlocktradeForChainOfForwards
  else if byte = 0x47 then .legOfChainOfForwards
  else if byte = 0x4A then .legOfCrossingOfForeignCurrencyStrategy
  else if byte = 0x4B then .sellLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4C then .buyLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4E then .legOfForeignCurrencyStrategy
  else if byte = 0x51 then .legOfForeignCurrencyStrategy_51
  else if byte = 0x52 then .legOfCrossingOfChainOfForwards
  else if byte = 0x53 then .sellLegAutoEntryOfChainOfForwards
  else if byte = 0x54 then .buyLegAutoEntryOfChainOfForwards
  else if byte = 0x55 then .legOfAuctionOfChainOfForwards
  else if byte = 0x56 then .legOfRoundOfChainOfForwards
  else if byte = 0x57 then .chainsOfForwards
  else if byte = 0x59 then .legOfRolloverCrossing
  else if byte = 0x5A then .sellLegAutoEntryOfRollover
  else if byte = 0x61 then .buyLegAutoEntryOfRollover
  else if byte = 0x62 then .legOfRoundOfRollover
  else if byte = 0x63 then .depthOfRoundOfChainOfForwards
  else if byte = 0x64 then .tradingOfChainOfForwards
  else if byte = 0x65 then .depthOfRound
  else if byte = 0x66 then .roundOfChainOfForwards
  else if byte = 0x67 then .rolloverSentra
  else if byte = 0x68 then .typeRound
  else if byte = 0x69 then .auctions
  else if byte = 0x6A then .legOfBlockTradeOfRollover
  else if byte = 0x6B then .legOfBlockTradeOfForeignCurrencyStrategy
  else if byte = 0x6C then .blockTradeOfForeignCurrencyStrategy
  else if byte = 0x6D then .blockTradeOfChainOfForwards
  else if byte = 0x6E then .blocktradeOfRollover
  else if byte = 0x6F then .crossingOfChainOfForwards
  else if byte = 0x70 then .sellAutoEntryOfChainOfForwards
  else if byte = 0x71 then .buyAutoEntryOfChainOfForwards
  else if byte = 0x72 then .swapBlockTrade
  else if byte = 0x73 then .swapBlockTradeWithContinuousCoupon
  else if byte = 0x74 then .blockTradeOfUnwind
  else if byte = 0x75 then .blockTradeOfSubstitution
  else if byte = 0x7A then .voiceOver
  else if byte = 0x23 then .firmOrder
  else if byte = 0x49 then .ipoCross
  else if byte = 0x2B then .unintentionalSelfCross
  else if byte = 0x26 then .withoutConcertation
  else if byte = 0x28 then .inavToClosingPriceTrading
  else .inavAfterClosing

def ofByte (byte : UInt8) : ConcertationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ConcertationType) : ofByte value.toByte = value := by
  cases value with
  | crossingOperation => decide
  | orderClosing => decide
  | operationAtClosingPrice => decide
  | operationAfterClosing => decide
  | operationAtMediumPrice => decide
  | operationAtAveragePriceForTheDay => decide
  | blockOperationsByException => decide
  | vwapOperationsByException => decide
  | twapOperationsByException => decide
  | basketTrading => decide
  | otcRecentOperations => decide
  | otcAgreedOperations => decide
  | buyAutoEntry => decide
  | sellAutoEntry => decide
  | blockTrade => decide
  | legOfBlocktradeForChainOfForwards => decide
  | legOfChainOfForwards => decide
  | legOfCrossingOfForeignCurrencyStrategy => decide
  | sellLegAutoEntryOfForeignCurrencyStrategy => decide
  | buyLegAutoEntryOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy_51 => decide
  | legOfCrossingOfChainOfForwards => decide
  | sellLegAutoEntryOfChainOfForwards => decide
  | buyLegAutoEntryOfChainOfForwards => decide
  | legOfAuctionOfChainOfForwards => decide
  | legOfRoundOfChainOfForwards => decide
  | chainsOfForwards => decide
  | legOfRolloverCrossing => decide
  | sellLegAutoEntryOfRollover => decide
  | buyLegAutoEntryOfRollover => decide
  | legOfRoundOfRollover => decide
  | depthOfRoundOfChainOfForwards => decide
  | tradingOfChainOfForwards => decide
  | depthOfRound => decide
  | roundOfChainOfForwards => decide
  | rolloverSentra => decide
  | typeRound => decide
  | auctions => decide
  | legOfBlockTradeOfRollover => decide
  | legOfBlockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfChainOfForwards => decide
  | blocktradeOfRollover => decide
  | crossingOfChainOfForwards => decide
  | sellAutoEntryOfChainOfForwards => decide
  | buyAutoEntryOfChainOfForwards => decide
  | swapBlockTrade => decide
  | swapBlockTradeWithContinuousCoupon => decide
  | blockTradeOfUnwind => decide
  | blockTradeOfSubstitution => decide
  | voiceOver => decide
  | firmOrder => decide
  | ipoCross => decide
  | unintentionalSelfCross => decide
  | withoutConcertation => decide
  | inavToClosingPriceTrading => decide
  | inavAfterClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ConcertationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ConcertationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ConcertationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ConcertationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ConcertationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ConcertationType

/-- Operation Type: one byte code -/
def OperationType.codes : List UInt8 :=
  [0x43, 0x4F, 0x52, 0x41, 0x53, 0x46, 0x48, 0x4D, 0x58, 0x50, 0x44, 0x4E]

inductive OperationType where
  | cash -- Cash
  | publicOffering -- Public Offering
  | registrationOperation -- Registration Operation
  | overallocation -- Overallocation
  | reciprocalSubscription -- Reciprocal Subscription
  | publicBuyOffering -- Public Buy Offering
  | tradesAtClosing -- Trades At Closing
  | mediumPrice -- Medium Price
  | operationByException -- Operation By Exception
  | averageForTheDay -- Average For The Day
  | afterClosing -- After Closing
  | inavTrading -- Inav Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ OperationType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OperationType

def toByte : OperationType → UInt8
  | .cash => 0x43
  | .publicOffering => 0x4F
  | .registrationOperation => 0x52
  | .overallocation => 0x41
  | .reciprocalSubscription => 0x53
  | .publicBuyOffering => 0x46
  | .tradesAtClosing => 0x48
  | .mediumPrice => 0x4D
  | .operationByException => 0x58
  | .averageForTheDay => 0x50
  | .afterClosing => 0x44
  | .inavTrading => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OperationType :=
  if byte = 0x43 then .cash
  else if byte = 0x4F then .publicOffering
  else if byte = 0x52 then .registrationOperation
  else if byte = 0x41 then .overallocation
  else if byte = 0x53 then .reciprocalSubscription
  else if byte = 0x46 then .publicBuyOffering
  else if byte = 0x48 then .tradesAtClosing
  else if byte = 0x4D then .mediumPrice
  else if byte = 0x58 then .operationByException
  else if byte = 0x50 then .averageForTheDay
  else if byte = 0x44 then .afterClosing
  else .inavTrading

def ofByte (byte : UInt8) : OperationType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OperationType) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | publicOffering => decide
  | registrationOperation => decide
  | overallocation => decide
  | reciprocalSubscription => decide
  | publicBuyOffering => decide
  | tradesAtClosing => decide
  | mediumPrice => decide
  | operationByException => decide
  | averageForTheDay => decide
  | afterClosing => decide
  | inavTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OperationType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OperationType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OperationType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OperationType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OperationType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OperationType

/-- Settlement: one byte code -/
def Settlement.codes : List UInt8 :=
  [0x4D, 0x32, 0x34, 0x37, 0x39, 0x31]

inductive Settlement where
  | sameDay -- Same Day
  | twentyFourHours -- Twenty Four Hours
  | fortyEightHours -- Forty Eight Hours
  | seventyTwoHours -- Seventy Two Hours
  | ninetySixHours -- Ninety Six Hours
  | oneHundredTwentyHours -- One Hundred Twenty Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ Settlement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Settlement

def toByte : Settlement → UInt8
  | .sameDay => 0x4D
  | .twentyFourHours => 0x32
  | .fortyEightHours => 0x34
  | .seventyTwoHours => 0x37
  | .ninetySixHours => 0x39
  | .oneHundredTwentyHours => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Settlement :=
  if byte = 0x4D then .sameDay
  else if byte = 0x32 then .twentyFourHours
  else if byte = 0x34 then .fortyEightHours
  else if byte = 0x37 then .seventyTwoHours
  else if byte = 0x39 then .ninetySixHours
  else .oneHundredTwentyHours

def ofByte (byte : UInt8) : Settlement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Settlement) : ofByte value.toByte = value := by
  cases value with
  | sameDay => decide
  | twentyFourHours => decide
  | fortyEightHours => decide
  | seventyTwoHours => decide
  | ninetySixHours => decide
  | oneHundredTwentyHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Settlement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Settlement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Settlement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Settlement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Settlement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Settlement

/-- Auction Indicator: one byte code -/
def AuctionIndicator.codes : List UInt8 :=
  [0x50, 0x53, 0x20, 0x4E]

inductive AuctionIndicator where
  | openingAuction -- Opening Auction
  | otherAuctions -- Other Auctions
  | continuousMarket -- Continuous Market
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionIndicator

def toByte : AuctionIndicator → UInt8
  | .openingAuction => 0x50
  | .otherAuctions => 0x53
  | .continuousMarket => 0x20
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionIndicator :=
  if byte = 0x50 then .openingAuction
  else if byte = 0x53 then .otherAuctions
  else if byte = 0x20 then .continuousMarket
  else .notApplicable

def ofByte (byte : UInt8) : AuctionIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionIndicator) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | otherAuctions => decide
  | continuousMarket => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionIndicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionIndicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionIndicator

/-- Offer Type: one byte code -/
def OfferType.codes : List UInt8 :=
  [0x50, 0x52, 0x43, 0x41, 0x53]

inductive OfferType where
  | publicOffering -- Public Offering
  | registrationOperation -- Registration Operation
  | buyPublicOffering -- Buy Public Offering
  | overallocation -- Overallocation
  | reciprocalSubscription -- Reciprocal Subscription
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferType

def toByte : OfferType → UInt8
  | .publicOffering => 0x50
  | .registrationOperation => 0x52
  | .buyPublicOffering => 0x43
  | .overallocation => 0x41
  | .reciprocalSubscription => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferType :=
  if byte = 0x50 then .publicOffering
  else if byte = 0x52 then .registrationOperation
  else if byte = 0x43 then .buyPublicOffering
  else if byte = 0x41 then .overallocation
  else .reciprocalSubscription

def ofByte (byte : UInt8) : OfferType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferType) : ofByte value.toByte = value := by
  cases value with
  | publicOffering => decide
  | registrationOperation => decide
  | buyPublicOffering => decide
  | overallocation => decide
  | reciprocalSubscription => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OfferType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OfferType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OfferType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OfferType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OfferType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OfferType

/-- Income: one byte code -/
def Income.codes : List UInt8 :=
  [0x56, 0x46, 0x57]

inductive Income where
  | variableIncome -- Variable Income
  | fixedIncome -- Fixed Income
  | warrants -- Warrants
  | unlisted (byte : { byte : UInt8 // byte ∉ Income.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Income

def toByte : Income → UInt8
  | .variableIncome => 0x56
  | .fixedIncome => 0x46
  | .warrants => 0x57
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Income :=
  if byte = 0x56 then .variableIncome
  else if byte = 0x46 then .fixedIncome
  else .warrants

def ofByte (byte : UInt8) : Income :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Income) : ofByte value.toByte = value := by
  cases value with
  | variableIncome => decide
  | fixedIncome => decide
  | warrants => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Income) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Income × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Income) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Income) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Income) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Income

/-- Movement: one byte code -/
def Movement.codes : List UInt8 :=
  [0x41, 0x55, 0x43, 0x42]

inductive Movement where
  | registryOperation -- Registry Operation
  | operationAuthorization -- Operation Authorization
  | placementOperation -- Placement Operation
  | deleteOperation -- Delete Operation
  | unlisted (byte : { byte : UInt8 // byte ∉ Movement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Movement

def toByte : Movement → UInt8
  | .registryOperation => 0x41
  | .operationAuthorization => 0x55
  | .placementOperation => 0x43
  | .deleteOperation => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Movement :=
  if byte = 0x41 then .registryOperation
  else if byte = 0x55 then .operationAuthorization
  else if byte = 0x43 then .placementOperation
  else .deleteOperation

def ofByte (byte : UInt8) : Movement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Movement) : ofByte value.toByte = value := by
  cases value with
  | registryOperation => decide
  | operationAuthorization => decide
  | placementOperation => decide
  | deleteOperation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Movement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Movement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Movement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Movement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Movement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Movement

/-- Virtual Trades Status: one byte code -/
def VirtualTradesStatus.codes : List UInt8 :=
  [0x41, 0x42]

inductive VirtualTradesStatus where
  | addition -- Addition
  | deletion -- Deletion
  | unlisted (byte : { byte : UInt8 // byte ∉ VirtualTradesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace VirtualTradesStatus

def toByte : VirtualTradesStatus → UInt8
  | .addition => 0x41
  | .deletion => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : VirtualTradesStatus :=
  if byte = 0x41 then .addition
  else .deletion

def ofByte (byte : UInt8) : VirtualTradesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : VirtualTradesStatus) : ofByte value.toByte = value := by
  cases value with
  | addition => decide
  | deletion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : VirtualTradesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (VirtualTradesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : VirtualTradesStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : VirtualTradesStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : VirtualTradesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end VirtualTradesStatus

/-- Concertation: one byte code -/
def Concertation.codes : List UInt8 :=
  [0x43, 0x4F, 0x48, 0x44, 0x4D, 0x50, 0x58, 0x76, 0x77, 0x25, 0x78, 0x79, 0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B, 0x4C, 0x4E, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x7A, 0x23, 0x49, 0x2B, 0x26, 0x28, 0x29]

inductive Concertation where
  | crossingOperation -- Crossing Operation
  | orderClosing -- Order Closing
  | operationAtClosingPrice -- Operation At Closing Price
  | operationAfterClosing -- Operation After Closing
  | operationAtMediumPrice -- Operation At Medium Price
  | operationAtAveragePriceForTheDay -- Operation At Average Price For The Day
  | blockOperationsByException -- Block Operations By Exception
  | vwapOperationsByException -- Vwap Operations By Exception
  | twapOperationsByException -- Twap Operations By Exception
  | basketTrading -- Basket Trading
  | otcRecentOperations -- Otc Recent Operations
  | otcAgreedOperations -- Otc Agreed Operations
  | buyAutoEntry -- Buy Auto Entry
  | sellAutoEntry -- Sell Auto Entry
  | blockTrade -- Block Trade
  | legOfBlocktradeForChainOfForwards -- Leg Of Blocktrade For Chain Of Forwards
  | legOfChainOfForwards -- Leg Of Chain Of Forwards
  | legOfCrossingOfForeignCurrencyStrategy -- Leg Of Crossing Of Foreign Currency Strategy
  | sellLegAutoEntryOfForeignCurrencyStrategy -- Sell Leg Auto Entry Of Foreign Currency Strategy
  | buyLegAutoEntryOfForeignCurrencyStrategy -- Buy Leg Auto Entry Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy -- Leg Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy_51 -- Leg Of Foreign Currency Strategy
  | legOfCrossingOfChainOfForwards -- Leg Of Crossing Of Chain Of Forwards
  | sellLegAutoEntryOfChainOfForwards -- Sell Leg Auto Entry Of Chain Of Forwards
  | buyLegAutoEntryOfChainOfForwards -- Buy Leg Auto Entry Of Chain Of Forwards
  | legOfAuctionOfChainOfForwards -- Leg Of Auction Of Chain Of Forwards
  | legOfRoundOfChainOfForwards -- Leg Of Round Of Chain Of Forwards
  | chainsOfForwards -- Chains Of Forwards
  | legOfRolloverCrossing -- Leg Of Rollover Crossing
  | sellLegAutoEntryOfRollover -- Sell Leg Auto Entry Of Rollover
  | buyLegAutoEntryOfRollover -- Buy Leg Auto Entry Of Rollover
  | legOfRoundOfRollover -- Leg Of Round Of Rollover
  | depthOfRoundOfChainOfForwards -- Depth Of Round Of Chain Of Forwards
  | tradingOfChainOfForwards -- Trading Of Chain Of Forwards
  | depthOfRound -- Depth Of Round
  | roundOfChainOfForwards -- Round Of Chain Of Forwards
  | rolloverSentra -- Rollover Sentra
  | typeRound -- Type Round
  | auctions -- Auctions
  | legOfBlockTradeOfRollover -- Leg Of Block Trade Of Rollover
  | legOfBlockTradeOfForeignCurrencyStrategy -- Leg Of Block Trade Of Foreign Currency Strategy
  | blockTradeOfForeignCurrencyStrategy -- Block Trade Of Foreign Currency Strategy
  | blockTradeOfChainOfForwards -- Block Trade Of Chain Of Forwards
  | blocktradeOfRollover -- Blocktrade Of Rollover
  | crossingOfChainOfForwards -- Crossing Of Chain Of Forwards
  | sellAutoEntryOfChainOfForwards -- Sell Auto Entry Of Chain Of Forwards
  | buyAutoEntryOfChainOfForwards -- Buy Auto Entry Of Chain Of Forwards
  | swapBlockTrade -- Swap Block Trade
  | swapBlockTradeWithContinuousCoupon -- Swap Block Trade With Continuous Coupon
  | blockTradeOfUnwind -- Block Trade Of Unwind
  | blockTradeOfSubstitution -- Block Trade Of Substitution
  | voiceOver -- Voice Over
  | firmOrder -- Firm Order
  | ipoCross -- Ipo Cross
  | unintentionalSelfCross -- Unintentional Self Cross
  | withoutConcertation -- Without Concertation
  | inavToClosingPriceTrading -- Inav To Closing Price Trading
  | inavAfterClosing -- Inav After Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ Concertation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Concertation

def toByte : Concertation → UInt8
  | .crossingOperation => 0x43
  | .orderClosing => 0x4F
  | .operationAtClosingPrice => 0x48
  | .operationAfterClosing => 0x44
  | .operationAtMediumPrice => 0x4D
  | .operationAtAveragePriceForTheDay => 0x50
  | .blockOperationsByException => 0x58
  | .vwapOperationsByException => 0x76
  | .twapOperationsByException => 0x77
  | .basketTrading => 0x25
  | .otcRecentOperations => 0x78
  | .otcAgreedOperations => 0x79
  | .buyAutoEntry => 0x41
  | .sellAutoEntry => 0x42
  | .blockTrade => 0x45
  | .legOfBlocktradeForChainOfForwards => 0x46
  | .legOfChainOfForwards => 0x47
  | .legOfCrossingOfForeignCurrencyStrategy => 0x4A
  | .sellLegAutoEntryOfForeignCurrencyStrategy => 0x4B
  | .buyLegAutoEntryOfForeignCurrencyStrategy => 0x4C
  | .legOfForeignCurrencyStrategy => 0x4E
  | .legOfForeignCurrencyStrategy_51 => 0x51
  | .legOfCrossingOfChainOfForwards => 0x52
  | .sellLegAutoEntryOfChainOfForwards => 0x53
  | .buyLegAutoEntryOfChainOfForwards => 0x54
  | .legOfAuctionOfChainOfForwards => 0x55
  | .legOfRoundOfChainOfForwards => 0x56
  | .chainsOfForwards => 0x57
  | .legOfRolloverCrossing => 0x59
  | .sellLegAutoEntryOfRollover => 0x5A
  | .buyLegAutoEntryOfRollover => 0x61
  | .legOfRoundOfRollover => 0x62
  | .depthOfRoundOfChainOfForwards => 0x63
  | .tradingOfChainOfForwards => 0x64
  | .depthOfRound => 0x65
  | .roundOfChainOfForwards => 0x66
  | .rolloverSentra => 0x67
  | .typeRound => 0x68
  | .auctions => 0x69
  | .legOfBlockTradeOfRollover => 0x6A
  | .legOfBlockTradeOfForeignCurrencyStrategy => 0x6B
  | .blockTradeOfForeignCurrencyStrategy => 0x6C
  | .blockTradeOfChainOfForwards => 0x6D
  | .blocktradeOfRollover => 0x6E
  | .crossingOfChainOfForwards => 0x6F
  | .sellAutoEntryOfChainOfForwards => 0x70
  | .buyAutoEntryOfChainOfForwards => 0x71
  | .swapBlockTrade => 0x72
  | .swapBlockTradeWithContinuousCoupon => 0x73
  | .blockTradeOfUnwind => 0x74
  | .blockTradeOfSubstitution => 0x75
  | .voiceOver => 0x7A
  | .firmOrder => 0x23
  | .ipoCross => 0x49
  | .unintentionalSelfCross => 0x2B
  | .withoutConcertation => 0x26
  | .inavToClosingPriceTrading => 0x28
  | .inavAfterClosing => 0x29
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Concertation :=
  if byte = 0x43 then .crossingOperation
  else if byte = 0x4F then .orderClosing
  else if byte = 0x48 then .operationAtClosingPrice
  else if byte = 0x44 then .operationAfterClosing
  else if byte = 0x4D then .operationAtMediumPrice
  else if byte = 0x50 then .operationAtAveragePriceForTheDay
  else if byte = 0x58 then .blockOperationsByException
  else if byte = 0x76 then .vwapOperationsByException
  else if byte = 0x77 then .twapOperationsByException
  else if byte = 0x25 then .basketTrading
  else if byte = 0x78 then .otcRecentOperations
  else if byte = 0x79 then .otcAgreedOperations
  else if byte = 0x41 then .buyAutoEntry
  else if byte = 0x42 then .sellAutoEntry
  else if byte = 0x45 then .blockTrade
  else if byte = 0x46 then .legOfBlocktradeForChainOfForwards
  else if byte = 0x47 then .legOfChainOfForwards
  else if byte = 0x4A then .legOfCrossingOfForeignCurrencyStrategy
  else if byte = 0x4B then .sellLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4C then .buyLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4E then .legOfForeignCurrencyStrategy
  else if byte = 0x51 then .legOfForeignCurrencyStrategy_51
  else if byte = 0x52 then .legOfCrossingOfChainOfForwards
  else if byte = 0x53 then .sellLegAutoEntryOfChainOfForwards
  else if byte = 0x54 then .buyLegAutoEntryOfChainOfForwards
  else if byte = 0x55 then .legOfAuctionOfChainOfForwards
  else if byte = 0x56 then .legOfRoundOfChainOfForwards
  else if byte = 0x57 then .chainsOfForwards
  else if byte = 0x59 then .legOfRolloverCrossing
  else if byte = 0x5A then .sellLegAutoEntryOfRollover
  else if byte = 0x61 then .buyLegAutoEntryOfRollover
  else if byte = 0x62 then .legOfRoundOfRollover
  else if byte = 0x63 then .depthOfRoundOfChainOfForwards
  else if byte = 0x64 then .tradingOfChainOfForwards
  else if byte = 0x65 then .depthOfRound
  else if byte = 0x66 then .roundOfChainOfForwards
  else if byte = 0x67 then .rolloverSentra
  else if byte = 0x68 then .typeRound
  else if byte = 0x69 then .auctions
  else if byte = 0x6A then .legOfBlockTradeOfRollover
  else if byte = 0x6B then .legOfBlockTradeOfForeignCurrencyStrategy
  else if byte = 0x6C then .blockTradeOfForeignCurrencyStrategy
  else if byte = 0x6D then .blockTradeOfChainOfForwards
  else if byte = 0x6E then .blocktradeOfRollover
  else if byte = 0x6F then .crossingOfChainOfForwards
  else if byte = 0x70 then .sellAutoEntryOfChainOfForwards
  else if byte = 0x71 then .buyAutoEntryOfChainOfForwards
  else if byte = 0x72 then .swapBlockTrade
  else if byte = 0x73 then .swapBlockTradeWithContinuousCoupon
  else if byte = 0x74 then .blockTradeOfUnwind
  else if byte = 0x75 then .blockTradeOfSubstitution
  else if byte = 0x7A then .voiceOver
  else if byte = 0x23 then .firmOrder
  else if byte = 0x49 then .ipoCross
  else if byte = 0x2B then .unintentionalSelfCross
  else if byte = 0x26 then .withoutConcertation
  else if byte = 0x28 then .inavToClosingPriceTrading
  else .inavAfterClosing

def ofByte (byte : UInt8) : Concertation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Concertation) : ofByte value.toByte = value := by
  cases value with
  | crossingOperation => decide
  | orderClosing => decide
  | operationAtClosingPrice => decide
  | operationAfterClosing => decide
  | operationAtMediumPrice => decide
  | operationAtAveragePriceForTheDay => decide
  | blockOperationsByException => decide
  | vwapOperationsByException => decide
  | twapOperationsByException => decide
  | basketTrading => decide
  | otcRecentOperations => decide
  | otcAgreedOperations => decide
  | buyAutoEntry => decide
  | sellAutoEntry => decide
  | blockTrade => decide
  | legOfBlocktradeForChainOfForwards => decide
  | legOfChainOfForwards => decide
  | legOfCrossingOfForeignCurrencyStrategy => decide
  | sellLegAutoEntryOfForeignCurrencyStrategy => decide
  | buyLegAutoEntryOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy_51 => decide
  | legOfCrossingOfChainOfForwards => decide
  | sellLegAutoEntryOfChainOfForwards => decide
  | buyLegAutoEntryOfChainOfForwards => decide
  | legOfAuctionOfChainOfForwards => decide
  | legOfRoundOfChainOfForwards => decide
  | chainsOfForwards => decide
  | legOfRolloverCrossing => decide
  | sellLegAutoEntryOfRollover => decide
  | buyLegAutoEntryOfRollover => decide
  | legOfRoundOfRollover => decide
  | depthOfRoundOfChainOfForwards => decide
  | tradingOfChainOfForwards => decide
  | depthOfRound => decide
  | roundOfChainOfForwards => decide
  | rolloverSentra => decide
  | typeRound => decide
  | auctions => decide
  | legOfBlockTradeOfRollover => decide
  | legOfBlockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfChainOfForwards => decide
  | blocktradeOfRollover => decide
  | crossingOfChainOfForwards => decide
  | sellAutoEntryOfChainOfForwards => decide
  | buyAutoEntryOfChainOfForwards => decide
  | swapBlockTrade => decide
  | swapBlockTradeWithContinuousCoupon => decide
  | blockTradeOfUnwind => decide
  | blockTradeOfSubstitution => decide
  | voiceOver => decide
  | firmOrder => decide
  | ipoCross => decide
  | unintentionalSelfCross => decide
  | withoutConcertation => decide
  | inavToClosingPriceTrading => decide
  | inavAfterClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Concertation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Concertation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Concertation) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Concertation) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Concertation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Concertation

/-- Direction: one byte code -/
def Direction.codes : List UInt8 :=
  [0x43, 0x56]

inductive Direction where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Direction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Direction

def toByte : Direction → UInt8
  | .buy => 0x43
  | .sell => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Direction :=
  if byte = 0x43 then .buy
  else .sell

def ofByte (byte : UInt8) : Direction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Direction) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Direction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Direction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Direction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Direction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Direction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Direction

/-- Offer Direction: one byte code -/
def OfferDirection.codes : List UInt8 :=
  [0x43, 0x56]

inductive OfferDirection where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OfferDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OfferDirection

def toByte : OfferDirection → UInt8
  | .buy => 0x43
  | .sell => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OfferDirection :=
  if byte = 0x43 then .buy
  else .sell

def ofByte (byte : UInt8) : OfferDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OfferDirection) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OfferDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OfferDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OfferDirection) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OfferDirection) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OfferDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OfferDirection

/-- Currency Type: one byte code -/
def CurrencyType.codes : List UInt8 :=
  [0x4E, 0x44]

inductive CurrencyType where
  | mexicanCurrency -- Mexican Currency
  | dollar -- Dollar
  | unlisted (byte : { byte : UInt8 // byte ∉ CurrencyType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CurrencyType

def toByte : CurrencyType → UInt8
  | .mexicanCurrency => 0x4E
  | .dollar => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CurrencyType :=
  if byte = 0x4E then .mexicanCurrency
  else .dollar

def ofByte (byte : UInt8) : CurrencyType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CurrencyType) : ofByte value.toByte = value := by
  cases value with
  | mexicanCurrency => decide
  | dollar => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CurrencyType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CurrencyType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CurrencyType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CurrencyType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CurrencyType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CurrencyType

/-- Leg Type: one byte code -/
def LegType.codes : List UInt8 :=
  [0x4C, 0x43, 0x58, 0x50, 0x20]

inductive LegType where
  | longLeg -- Long Leg
  | shortLeg -- Short Leg
  | forwardsChainLeg -- Forwards Chain Leg
  | parentStrategy -- Parent Strategy
  | notGeneratedFromAStrategy -- Not Generated From A Strategy
  | unlisted (byte : { byte : UInt8 // byte ∉ LegType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegType

def toByte : LegType → UInt8
  | .longLeg => 0x4C
  | .shortLeg => 0x43
  | .forwardsChainLeg => 0x58
  | .parentStrategy => 0x50
  | .notGeneratedFromAStrategy => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegType :=
  if byte = 0x4C then .longLeg
  else if byte = 0x43 then .shortLeg
  else if byte = 0x58 then .forwardsChainLeg
  else if byte = 0x50 then .parentStrategy
  else .notGeneratedFromAStrategy

def ofByte (byte : UInt8) : LegType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegType) : ofByte value.toByte = value := by
  cases value with
  | longLeg => decide
  | shortLeg => decide
  | forwardsChainLeg => decide
  | parentStrategy => decide
  | notGeneratedFromAStrategy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LegType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LegType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegType

/-- Trend: one byte code -/
def Trend.codes : List UInt8 :=
  [0x41, 0x42, 0x53, 0x20]

inductive Trend where
  | increase -- Increase
  | decrease -- Decrease
  | withoutChange -- Without Change
  | withoutOperation -- Without Operation
  | unlisted (byte : { byte : UInt8 // byte ∉ Trend.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Trend

def toByte : Trend → UInt8
  | .increase => 0x41
  | .decrease => 0x42
  | .withoutChange => 0x53
  | .withoutOperation => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Trend :=
  if byte = 0x41 then .increase
  else if byte = 0x42 then .decrease
  else if byte = 0x53 then .withoutChange
  else .withoutOperation

def ofByte (byte : UInt8) : Trend :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Trend) : ofByte value.toByte = value := by
  cases value with
  | increase => decide
  | decrease => decide
  | withoutChange => decide
  | withoutOperation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Trend) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Trend × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Trend) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Trend) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Trend) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Trend

/-- Indices Status: one byte code -/
def IndicesStatus.codes : List UInt8 :=
  [0x41, 0x50, 0x43, 0x44]

inductive IndicesStatus where
  | previous -- Previous
  | preliminary -- Preliminary
  | preliminaryFigures -- Preliminary Figures
  | final -- Final
  | unlisted (byte : { byte : UInt8 // byte ∉ IndicesStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace IndicesStatus

def toByte : IndicesStatus → UInt8
  | .previous => 0x41
  | .preliminary => 0x50
  | .preliminaryFigures => 0x43
  | .final => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : IndicesStatus :=
  if byte = 0x41 then .previous
  else if byte = 0x50 then .preliminary
  else if byte = 0x43 then .preliminaryFigures
  else .final

def ofByte (byte : UInt8) : IndicesStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : IndicesStatus) : ofByte value.toByte = value := by
  cases value with
  | previous => decide
  | preliminary => decide
  | preliminaryFigures => decide
  | final => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : IndicesStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (IndicesStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : IndicesStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : IndicesStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : IndicesStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end IndicesStatus

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

/-- Multiple Type: one byte code -/
def MultipleType.codes : List UInt8 :=
  [0x45, 0x53]

inductive MultipleType where
  | multipleOfMarketByTransmitter -- Multiple Of Market By Transmitter
  | multipleOfMarketBySector -- Multiple Of Market By Sector
  | unlisted (byte : { byte : UInt8 // byte ∉ MultipleType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MultipleType

def toByte : MultipleType → UInt8
  | .multipleOfMarketByTransmitter => 0x45
  | .multipleOfMarketBySector => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MultipleType :=
  if byte = 0x45 then .multipleOfMarketByTransmitter
  else .multipleOfMarketBySector

def ofByte (byte : UInt8) : MultipleType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MultipleType) : ofByte value.toByte = value := by
  cases value with
  | multipleOfMarketByTransmitter => decide
  | multipleOfMarketBySector => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MultipleType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MultipleType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MultipleType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MultipleType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MultipleType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MultipleType

/-- Rebalance: one byte code -/
def Rebalance.codes : List UInt8 :=
  [0x52, 0x4E]

inductive Rebalance where
  | rebalanced -- Rebalanced
  | notRebalanced -- Not Rebalanced
  | unlisted (byte : { byte : UInt8 // byte ∉ Rebalance.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Rebalance

def toByte : Rebalance → UInt8
  | .rebalanced => 0x52
  | .notRebalanced => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Rebalance :=
  if byte = 0x52 then .rebalanced
  else .notRebalanced

def ofByte (byte : UInt8) : Rebalance :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Rebalance) : ofByte value.toByte = value := by
  cases value with
  | rebalanced => decide
  | notRebalanced => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Rebalance) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Rebalance × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Rebalance) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Rebalance) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Rebalance) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Rebalance

/-- Bursatility Indices Sign: one byte code -/
def BursatilityIndicesSign.codes : List UInt8 :=
  [0x20, 0x5F]

inductive BursatilityIndicesSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ BursatilityIndicesSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BursatilityIndicesSign

def toByte : BursatilityIndicesSign → UInt8
  | .positive => 0x20
  | .negative => 0x5F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BursatilityIndicesSign :=
  if byte = 0x20 then .positive
  else .negative

def ofByte (byte : UInt8) : BursatilityIndicesSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BursatilityIndicesSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BursatilityIndicesSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BursatilityIndicesSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BursatilityIndicesSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BursatilityIndicesSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BursatilityIndicesSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BursatilityIndicesSign

/-- Beta Coefficient Sign: one byte code -/
def BetaCoefficientSign.codes : List UInt8 :=
  [0x20, 0x5F]

inductive BetaCoefficientSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ BetaCoefficientSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BetaCoefficientSign

def toByte : BetaCoefficientSign → UInt8
  | .positive => 0x20
  | .negative => 0x5F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BetaCoefficientSign :=
  if byte = 0x20 then .positive
  else .negative

def ofByte (byte : UInt8) : BetaCoefficientSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BetaCoefficientSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BetaCoefficientSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BetaCoefficientSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BetaCoefficientSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : BetaCoefficientSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : BetaCoefficientSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BetaCoefficientSign

/-- Correlation Coefficient Sign: one byte code -/
def CorrelationCoefficientSign.codes : List UInt8 :=
  [0x20, 0x5F]

inductive CorrelationCoefficientSign where
  | positive -- Positive
  | negative -- Negative
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrelationCoefficientSign.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrelationCoefficientSign

def toByte : CorrelationCoefficientSign → UInt8
  | .positive => 0x20
  | .negative => 0x5F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrelationCoefficientSign :=
  if byte = 0x20 then .positive
  else .negative

def ofByte (byte : UInt8) : CorrelationCoefficientSign :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrelationCoefficientSign) : ofByte value.toByte = value := by
  cases value with
  | positive => decide
  | negative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrelationCoefficientSign) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrelationCoefficientSign × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrelationCoefficientSign) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrelationCoefficientSign) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrelationCoefficientSign) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrelationCoefficientSign

/-- Sending: one byte code -/
def Sending.codes : List UInt8 :=
  [0x41, 0x43]

inductive Sending where
  | preopening -- Preopening
  | afterClosing -- After Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ Sending.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Sending

def toByte : Sending → UInt8
  | .preopening => 0x41
  | .afterClosing => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Sending :=
  if byte = 0x41 then .preopening
  else .afterClosing

def ofByte (byte : UInt8) : Sending :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Sending) : ofByte value.toByte = value := by
  cases value with
  | preopening => decide
  | afterClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Sending) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Sending × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Sending) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Sending) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Sending) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Sending

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

/-- Reference: one byte code -/
def Reference.codes : List UInt8 :=
  [0x4E, 0x4A, 0x56, 0x20]

inductive Reference where
  | previous -- Previous
  | adjusted -- Adjusted
  | adjustedNominalValue -- Adjusted Nominal Value
  | withoutPrice -- Without Price
  | unlisted (byte : { byte : UInt8 // byte ∉ Reference.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reference

def toByte : Reference → UInt8
  | .previous => 0x4E
  | .adjusted => 0x4A
  | .adjustedNominalValue => 0x56
  | .withoutPrice => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reference :=
  if byte = 0x4E then .previous
  else if byte = 0x4A then .adjusted
  else if byte = 0x56 then .adjustedNominalValue
  else .withoutPrice

def ofByte (byte : UInt8) : Reference :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reference) : ofByte value.toByte = value := by
  cases value with
  | previous => decide
  | adjusted => decide
  | adjustedNominalValue => decide
  | withoutPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reference) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reference × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reference) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Reference) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Reference) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reference

/-- Trades Rate Price: one byte code -/
def TradesRatePrice.codes : List UInt8 :=
  [0x54, 0x50, 0x20]

inductive TradesRatePrice where
  | rate -- Rate
  | price -- Price
  | byDefault -- By Default
  | unlisted (byte : { byte : UInt8 // byte ∉ TradesRatePrice.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradesRatePrice

def toByte : TradesRatePrice → UInt8
  | .rate => 0x54
  | .price => 0x50
  | .byDefault => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradesRatePrice :=
  if byte = 0x54 then .rate
  else if byte = 0x50 then .price
  else .byDefault

def ofByte (byte : UInt8) : TradesRatePrice :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradesRatePrice) : ofByte value.toByte = value := by
  cases value with
  | rate => decide
  | price => decide
  | byDefault => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradesRatePrice) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradesRatePrice × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradesRatePrice) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradesRatePrice) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradesRatePrice) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradesRatePrice

/-- Code Of Event: one byte code -/
def CodeOfEvent.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x4A, 0x4B, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

inductive CodeOfEvent where
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
  | unlisted (byte : { byte : UInt8 // byte ∉ CodeOfEvent.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CodeOfEvent

def toByte : CodeOfEvent → UInt8
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
def listed (byte : UInt8) : CodeOfEvent :=
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

def ofByte (byte : UInt8) : CodeOfEvent :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CodeOfEvent) : ofByte value.toByte = value := by
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

def encode (value : CodeOfEvent) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CodeOfEvent × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CodeOfEvent) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CodeOfEvent) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CodeOfEvent) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CodeOfEvent

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x52, 0x43, 0x49, 0x56]

inductive PriceType where
  | reference -- Reference
  | closingPrice -- Closing Price
  | inav -- Inav
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .reference => 0x52
  | .closingPrice => 0x43
  | .inav => 0x49
  | .volumeWeightedAveragePrice => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x52 then .reference
  else if byte = 0x43 then .closingPrice
  else if byte = 0x49 then .inav
  else .volumeWeightedAveragePrice

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | reference => decide
  | closingPrice => decide
  | inav => decide
  | volumeWeightedAveragePrice => decide
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

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x43, 0x41, 0x50, 0x45, 0x47, 0x54, 0x4E, 0x4B, 0x4D, 0x55, 0x4F, 0x56, 0x4C, 0x49, 0x42, 0x57, 0x58, 0x59, 0x52]

inductive Status where
  | bidsCancellation -- Bids Cancellation
  | openingBiddingSession -- Opening Bidding Session
  | preOpening -- Pre Opening
  | inAllotment -- In Allotment
  | assignedBiddingSession -- Assigned Bidding Session
  | endedBiddingSession -- Ended Bidding Session
  | ongoingTrading -- Ongoing Trading
  | biddingSessionDueToParametersBreaking -- Bidding Session Due To Parameters Breaking
  | ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays -- Ongoing Bidding Session Due To Operations Ceasing For More Than 20 Business Days
  | demergerBiddingSession -- Demerger Bidding Session
  | suspendedSeries -- Suspended Series
  | suspendedListing -- Suspended Listing
  | biddingSessionDueToBreach -- Bidding Session Due To Breach
  | withdrawalOfOrdersInAnOngoingBiddingSession -- Withdrawal Of Orders In An Ongoing Bidding Session
  | withdrawalOfOrdersInIntradayBiddingSession -- Withdrawal Of Orders In Intraday Bidding Session
  | awaitingNews -- Awaiting News
  | settlementBiddingSession -- Settlement Bidding Session
  | extraordinarySettlementBiddingSession -- Extraordinary Settlement Bidding Session
  | ckdesTotalBiddingSession -- Ckdes Total Bidding Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .bidsCancellation => 0x43
  | .openingBiddingSession => 0x41
  | .preOpening => 0x50
  | .inAllotment => 0x45
  | .assignedBiddingSession => 0x47
  | .endedBiddingSession => 0x54
  | .ongoingTrading => 0x4E
  | .biddingSessionDueToParametersBreaking => 0x4B
  | .ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays => 0x4D
  | .demergerBiddingSession => 0x55
  | .suspendedSeries => 0x4F
  | .suspendedListing => 0x56
  | .biddingSessionDueToBreach => 0x4C
  | .withdrawalOfOrdersInAnOngoingBiddingSession => 0x49
  | .withdrawalOfOrdersInIntradayBiddingSession => 0x42
  | .awaitingNews => 0x57
  | .settlementBiddingSession => 0x58
  | .extraordinarySettlementBiddingSession => 0x59
  | .ckdesTotalBiddingSession => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x43 then .bidsCancellation
  else if byte = 0x41 then .openingBiddingSession
  else if byte = 0x50 then .preOpening
  else if byte = 0x45 then .inAllotment
  else if byte = 0x47 then .assignedBiddingSession
  else if byte = 0x54 then .endedBiddingSession
  else if byte = 0x4E then .ongoingTrading
  else if byte = 0x4B then .biddingSessionDueToParametersBreaking
  else if byte = 0x4D then .ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays
  else if byte = 0x55 then .demergerBiddingSession
  else if byte = 0x4F then .suspendedSeries
  else if byte = 0x56 then .suspendedListing
  else if byte = 0x4C then .biddingSessionDueToBreach
  else if byte = 0x49 then .withdrawalOfOrdersInAnOngoingBiddingSession
  else if byte = 0x42 then .withdrawalOfOrdersInIntradayBiddingSession
  else if byte = 0x57 then .awaitingNews
  else if byte = 0x58 then .settlementBiddingSession
  else if byte = 0x59 then .extraordinarySettlementBiddingSession
  else .ckdesTotalBiddingSession

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | bidsCancellation => decide
  | openingBiddingSession => decide
  | preOpening => decide
  | inAllotment => decide
  | assignedBiddingSession => decide
  | endedBiddingSession => decide
  | ongoingTrading => decide
  | biddingSessionDueToParametersBreaking => decide
  | ongoingBiddingSessionDueToOperationsCeasingForMoreThan20BusinessDays => decide
  | demergerBiddingSession => decide
  | suspendedSeries => decide
  | suspendedListing => decide
  | biddingSessionDueToBreach => decide
  | withdrawalOfOrdersInAnOngoingBiddingSession => decide
  | withdrawalOfOrdersInIntradayBiddingSession => decide
  | awaitingNews => decide
  | settlementBiddingSession => decide
  | extraordinarySettlementBiddingSession => decide
  | ckdesTotalBiddingSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Status) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x4E, 0x48, 0x41, 0x42, 0x51, 0x53, 0x4D, 0x4F, 0x43, 0x49]

inductive Reason where
  | normalOperation -- Normal Operation
  | volatilityBiddingSession -- Volatility Bidding Session
  | startupOfTheVolatilityBiddingSession -- Startup Of The Volatility Bidding Session
  | endOfTheVolatilityBiddingSession -- End Of The Volatility Bidding Session
  | awaitingNews -- Awaiting News
  | staticPriceBandBreach -- Static Price Band Breach
  | suspensionDueToMarketsSurveillance -- Suspension Due To Markets Surveillance
  | suspensionFromTheMarketOfOrigin -- Suspension From The Market Of Origin
  | withoutCompliance -- Without Compliance
  | startupOfTheInterestNotice -- Startup Of The Interest Notice
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .normalOperation => 0x4E
  | .volatilityBiddingSession => 0x48
  | .startupOfTheVolatilityBiddingSession => 0x41
  | .endOfTheVolatilityBiddingSession => 0x42
  | .awaitingNews => 0x51
  | .staticPriceBandBreach => 0x53
  | .suspensionDueToMarketsSurveillance => 0x4D
  | .suspensionFromTheMarketOfOrigin => 0x4F
  | .withoutCompliance => 0x43
  | .startupOfTheInterestNotice => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x4E then .normalOperation
  else if byte = 0x48 then .volatilityBiddingSession
  else if byte = 0x41 then .startupOfTheVolatilityBiddingSession
  else if byte = 0x42 then .endOfTheVolatilityBiddingSession
  else if byte = 0x51 then .awaitingNews
  else if byte = 0x53 then .staticPriceBandBreach
  else if byte = 0x4D then .suspensionDueToMarketsSurveillance
  else if byte = 0x4F then .suspensionFromTheMarketOfOrigin
  else if byte = 0x43 then .withoutCompliance
  else .startupOfTheInterestNotice

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | normalOperation => decide
  | volatilityBiddingSession => decide
  | startupOfTheVolatilityBiddingSession => decide
  | endOfTheVolatilityBiddingSession => decide
  | awaitingNews => decide
  | staticPriceBandBreach => decide
  | suspensionDueToMarketsSurveillance => decide
  | suspensionFromTheMarketOfOrigin => decide
  | withoutCompliance => decide
  | startupOfTheInterestNotice => decide
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

/-- Type Of Warrant: one byte code -/
def TypeOfWarrant.codes : List UInt8 :=
  [0x43, 0x56]

inductive TypeOfWarrant where
  | purchase -- Purchase
  | sale -- Sale
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfWarrant.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfWarrant

def toByte : TypeOfWarrant → UInt8
  | .purchase => 0x43
  | .sale => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfWarrant :=
  if byte = 0x43 then .purchase
  else .sale

def ofByte (byte : UInt8) : TypeOfWarrant :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfWarrant) : ofByte value.toByte = value := by
  cases value with
  | purchase => decide
  | sale => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfWarrant) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfWarrant × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfWarrant) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfWarrant) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfWarrant) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfWarrant

/-- Marketability: one byte code -/
def Marketability.codes : List UInt8 :=
  [0x41, 0x4D, 0x42, 0x4E, 0x52, 0x20]

inductive Marketability where
  | high -- High
  | medium -- Medium
  | low -- Low
  | minimum -- Minimum
  | recentQuotation -- Recent Quotation
  | nullOrInapplicable -- Null Or Inapplicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Marketability.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Marketability

def toByte : Marketability → UInt8
  | .high => 0x41
  | .medium => 0x4D
  | .low => 0x42
  | .minimum => 0x4E
  | .recentQuotation => 0x52
  | .nullOrInapplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Marketability :=
  if byte = 0x41 then .high
  else if byte = 0x4D then .medium
  else if byte = 0x42 then .low
  else if byte = 0x4E then .minimum
  else if byte = 0x52 then .recentQuotation
  else .nullOrInapplicable

def ofByte (byte : UInt8) : Marketability :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Marketability) : ofByte value.toByte = value := by
  cases value with
  | high => decide
  | medium => decide
  | low => decide
  | minimum => decide
  | recentQuotation => decide
  | nullOrInapplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Marketability) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Marketability × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Marketability) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Marketability) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Marketability) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Marketability

/-- Exchange: one byte code -/
def Exchange.codes : List UInt8 :=
  [0x4D, 0x49]

inductive Exchange where
  | bmv -- Bmv
  | biva -- Biva
  | unlisted (byte : { byte : UInt8 // byte ∉ Exchange.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Exchange

def toByte : Exchange → UInt8
  | .bmv => 0x4D
  | .biva => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Exchange :=
  if byte = 0x4D then .bmv
  else .biva

def ofByte (byte : UInt8) : Exchange :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Exchange) : ofByte value.toByte = value := by
  cases value with
  | bmv => decide
  | biva => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Exchange) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Exchange × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Exchange) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Exchange) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Exchange) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Exchange

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

/-- Type Of Agreement: one byte code -/
def TypeOfAgreement.codes : List UInt8 :=
  [0x43, 0x4F, 0x48, 0x44, 0x4D, 0x50, 0x58, 0x76, 0x77, 0x25, 0x78, 0x79, 0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B, 0x4C, 0x4E, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x59, 0x5A, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x7A, 0x23, 0x49, 0x2B, 0x26, 0x28, 0x29]

inductive TypeOfAgreement where
  | crossingOperation -- Crossing Operation
  | orderClosing -- Order Closing
  | operationAtClosingPrice -- Operation At Closing Price
  | operationAfterClosing -- Operation After Closing
  | operationAtMediumPrice -- Operation At Medium Price
  | operationAtAveragePriceForTheDay -- Operation At Average Price For The Day
  | blockOperationsByException -- Block Operations By Exception
  | vwapOperationsByException -- Vwap Operations By Exception
  | twapOperationsByException -- Twap Operations By Exception
  | basketTrading -- Basket Trading
  | otcRecentOperations -- Otc Recent Operations
  | otcAgreedOperations -- Otc Agreed Operations
  | buyAutoEntry -- Buy Auto Entry
  | sellAutoEntry -- Sell Auto Entry
  | blockTrade -- Block Trade
  | legOfBlocktradeForChainOfForwards -- Leg Of Blocktrade For Chain Of Forwards
  | legOfChainOfForwards -- Leg Of Chain Of Forwards
  | legOfCrossingOfForeignCurrencyStrategy -- Leg Of Crossing Of Foreign Currency Strategy
  | sellLegAutoEntryOfForeignCurrencyStrategy -- Sell Leg Auto Entry Of Foreign Currency Strategy
  | buyLegAutoEntryOfForeignCurrencyStrategy -- Buy Leg Auto Entry Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy -- Leg Of Foreign Currency Strategy
  | legOfForeignCurrencyStrategy_51 -- Leg Of Foreign Currency Strategy
  | legOfCrossingOfChainOfForwards -- Leg Of Crossing Of Chain Of Forwards
  | sellLegAutoEntryOfChainOfForwards -- Sell Leg Auto Entry Of Chain Of Forwards
  | buyLegAutoEntryOfChainOfForwards -- Buy Leg Auto Entry Of Chain Of Forwards
  | legOfAuctionOfChainOfForwards -- Leg Of Auction Of Chain Of Forwards
  | legOfRoundOfChainOfForwards -- Leg Of Round Of Chain Of Forwards
  | chainsOfForwards -- Chains Of Forwards
  | legOfRolloverCrossing -- Leg Of Rollover Crossing
  | sellLegAutoEntryOfRollover -- Sell Leg Auto Entry Of Rollover
  | buyLegAutoEntryOfRollover -- Buy Leg Auto Entry Of Rollover
  | legOfRoundOfRollover -- Leg Of Round Of Rollover
  | depthOfRoundOfChainOfForwards -- Depth Of Round Of Chain Of Forwards
  | tradingOfChainOfForwards -- Trading Of Chain Of Forwards
  | depthOfRound -- Depth Of Round
  | roundOfChainOfForwards -- Round Of Chain Of Forwards
  | rolloverSentra -- Rollover Sentra
  | typeRound -- Type Round
  | auctions -- Auctions
  | legOfBlockTradeOfRollover -- Leg Of Block Trade Of Rollover
  | legOfBlockTradeOfForeignCurrencyStrategy -- Leg Of Block Trade Of Foreign Currency Strategy
  | blockTradeOfForeignCurrencyStrategy -- Block Trade Of Foreign Currency Strategy
  | blockTradeOfChainOfForwards -- Block Trade Of Chain Of Forwards
  | blocktradeOfRollover -- Blocktrade Of Rollover
  | crossingOfChainOfForwards -- Crossing Of Chain Of Forwards
  | sellAutoEntryOfChainOfForwards -- Sell Auto Entry Of Chain Of Forwards
  | buyAutoEntryOfChainOfForwards -- Buy Auto Entry Of Chain Of Forwards
  | swapBlockTrade -- Swap Block Trade
  | swapBlockTradeWithContinuousCoupon -- Swap Block Trade With Continuous Coupon
  | blockTradeOfUnwind -- Block Trade Of Unwind
  | blockTradeOfSubstitution -- Block Trade Of Substitution
  | voiceOver -- Voice Over
  | firmOrder -- Firm Order
  | ipoCross -- Ipo Cross
  | unintentionalSelfCross -- Unintentional Self Cross
  | withoutConcertation -- Without Concertation
  | inavToClosingPriceTrading -- Inav To Closing Price Trading
  | inavAfterClosing -- Inav After Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfAgreement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfAgreement

def toByte : TypeOfAgreement → UInt8
  | .crossingOperation => 0x43
  | .orderClosing => 0x4F
  | .operationAtClosingPrice => 0x48
  | .operationAfterClosing => 0x44
  | .operationAtMediumPrice => 0x4D
  | .operationAtAveragePriceForTheDay => 0x50
  | .blockOperationsByException => 0x58
  | .vwapOperationsByException => 0x76
  | .twapOperationsByException => 0x77
  | .basketTrading => 0x25
  | .otcRecentOperations => 0x78
  | .otcAgreedOperations => 0x79
  | .buyAutoEntry => 0x41
  | .sellAutoEntry => 0x42
  | .blockTrade => 0x45
  | .legOfBlocktradeForChainOfForwards => 0x46
  | .legOfChainOfForwards => 0x47
  | .legOfCrossingOfForeignCurrencyStrategy => 0x4A
  | .sellLegAutoEntryOfForeignCurrencyStrategy => 0x4B
  | .buyLegAutoEntryOfForeignCurrencyStrategy => 0x4C
  | .legOfForeignCurrencyStrategy => 0x4E
  | .legOfForeignCurrencyStrategy_51 => 0x51
  | .legOfCrossingOfChainOfForwards => 0x52
  | .sellLegAutoEntryOfChainOfForwards => 0x53
  | .buyLegAutoEntryOfChainOfForwards => 0x54
  | .legOfAuctionOfChainOfForwards => 0x55
  | .legOfRoundOfChainOfForwards => 0x56
  | .chainsOfForwards => 0x57
  | .legOfRolloverCrossing => 0x59
  | .sellLegAutoEntryOfRollover => 0x5A
  | .buyLegAutoEntryOfRollover => 0x61
  | .legOfRoundOfRollover => 0x62
  | .depthOfRoundOfChainOfForwards => 0x63
  | .tradingOfChainOfForwards => 0x64
  | .depthOfRound => 0x65
  | .roundOfChainOfForwards => 0x66
  | .rolloverSentra => 0x67
  | .typeRound => 0x68
  | .auctions => 0x69
  | .legOfBlockTradeOfRollover => 0x6A
  | .legOfBlockTradeOfForeignCurrencyStrategy => 0x6B
  | .blockTradeOfForeignCurrencyStrategy => 0x6C
  | .blockTradeOfChainOfForwards => 0x6D
  | .blocktradeOfRollover => 0x6E
  | .crossingOfChainOfForwards => 0x6F
  | .sellAutoEntryOfChainOfForwards => 0x70
  | .buyAutoEntryOfChainOfForwards => 0x71
  | .swapBlockTrade => 0x72
  | .swapBlockTradeWithContinuousCoupon => 0x73
  | .blockTradeOfUnwind => 0x74
  | .blockTradeOfSubstitution => 0x75
  | .voiceOver => 0x7A
  | .firmOrder => 0x23
  | .ipoCross => 0x49
  | .unintentionalSelfCross => 0x2B
  | .withoutConcertation => 0x26
  | .inavToClosingPriceTrading => 0x28
  | .inavAfterClosing => 0x29
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfAgreement :=
  if byte = 0x43 then .crossingOperation
  else if byte = 0x4F then .orderClosing
  else if byte = 0x48 then .operationAtClosingPrice
  else if byte = 0x44 then .operationAfterClosing
  else if byte = 0x4D then .operationAtMediumPrice
  else if byte = 0x50 then .operationAtAveragePriceForTheDay
  else if byte = 0x58 then .blockOperationsByException
  else if byte = 0x76 then .vwapOperationsByException
  else if byte = 0x77 then .twapOperationsByException
  else if byte = 0x25 then .basketTrading
  else if byte = 0x78 then .otcRecentOperations
  else if byte = 0x79 then .otcAgreedOperations
  else if byte = 0x41 then .buyAutoEntry
  else if byte = 0x42 then .sellAutoEntry
  else if byte = 0x45 then .blockTrade
  else if byte = 0x46 then .legOfBlocktradeForChainOfForwards
  else if byte = 0x47 then .legOfChainOfForwards
  else if byte = 0x4A then .legOfCrossingOfForeignCurrencyStrategy
  else if byte = 0x4B then .sellLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4C then .buyLegAutoEntryOfForeignCurrencyStrategy
  else if byte = 0x4E then .legOfForeignCurrencyStrategy
  else if byte = 0x51 then .legOfForeignCurrencyStrategy_51
  else if byte = 0x52 then .legOfCrossingOfChainOfForwards
  else if byte = 0x53 then .sellLegAutoEntryOfChainOfForwards
  else if byte = 0x54 then .buyLegAutoEntryOfChainOfForwards
  else if byte = 0x55 then .legOfAuctionOfChainOfForwards
  else if byte = 0x56 then .legOfRoundOfChainOfForwards
  else if byte = 0x57 then .chainsOfForwards
  else if byte = 0x59 then .legOfRolloverCrossing
  else if byte = 0x5A then .sellLegAutoEntryOfRollover
  else if byte = 0x61 then .buyLegAutoEntryOfRollover
  else if byte = 0x62 then .legOfRoundOfRollover
  else if byte = 0x63 then .depthOfRoundOfChainOfForwards
  else if byte = 0x64 then .tradingOfChainOfForwards
  else if byte = 0x65 then .depthOfRound
  else if byte = 0x66 then .roundOfChainOfForwards
  else if byte = 0x67 then .rolloverSentra
  else if byte = 0x68 then .typeRound
  else if byte = 0x69 then .auctions
  else if byte = 0x6A then .legOfBlockTradeOfRollover
  else if byte = 0x6B then .legOfBlockTradeOfForeignCurrencyStrategy
  else if byte = 0x6C then .blockTradeOfForeignCurrencyStrategy
  else if byte = 0x6D then .blockTradeOfChainOfForwards
  else if byte = 0x6E then .blocktradeOfRollover
  else if byte = 0x6F then .crossingOfChainOfForwards
  else if byte = 0x70 then .sellAutoEntryOfChainOfForwards
  else if byte = 0x71 then .buyAutoEntryOfChainOfForwards
  else if byte = 0x72 then .swapBlockTrade
  else if byte = 0x73 then .swapBlockTradeWithContinuousCoupon
  else if byte = 0x74 then .blockTradeOfUnwind
  else if byte = 0x75 then .blockTradeOfSubstitution
  else if byte = 0x7A then .voiceOver
  else if byte = 0x23 then .firmOrder
  else if byte = 0x49 then .ipoCross
  else if byte = 0x2B then .unintentionalSelfCross
  else if byte = 0x26 then .withoutConcertation
  else if byte = 0x28 then .inavToClosingPriceTrading
  else .inavAfterClosing

def ofByte (byte : UInt8) : TypeOfAgreement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfAgreement) : ofByte value.toByte = value := by
  cases value with
  | crossingOperation => decide
  | orderClosing => decide
  | operationAtClosingPrice => decide
  | operationAfterClosing => decide
  | operationAtMediumPrice => decide
  | operationAtAveragePriceForTheDay => decide
  | blockOperationsByException => decide
  | vwapOperationsByException => decide
  | twapOperationsByException => decide
  | basketTrading => decide
  | otcRecentOperations => decide
  | otcAgreedOperations => decide
  | buyAutoEntry => decide
  | sellAutoEntry => decide
  | blockTrade => decide
  | legOfBlocktradeForChainOfForwards => decide
  | legOfChainOfForwards => decide
  | legOfCrossingOfForeignCurrencyStrategy => decide
  | sellLegAutoEntryOfForeignCurrencyStrategy => decide
  | buyLegAutoEntryOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy => decide
  | legOfForeignCurrencyStrategy_51 => decide
  | legOfCrossingOfChainOfForwards => decide
  | sellLegAutoEntryOfChainOfForwards => decide
  | buyLegAutoEntryOfChainOfForwards => decide
  | legOfAuctionOfChainOfForwards => decide
  | legOfRoundOfChainOfForwards => decide
  | chainsOfForwards => decide
  | legOfRolloverCrossing => decide
  | sellLegAutoEntryOfRollover => decide
  | buyLegAutoEntryOfRollover => decide
  | legOfRoundOfRollover => decide
  | depthOfRoundOfChainOfForwards => decide
  | tradingOfChainOfForwards => decide
  | depthOfRound => decide
  | roundOfChainOfForwards => decide
  | rolloverSentra => decide
  | typeRound => decide
  | auctions => decide
  | legOfBlockTradeOfRollover => decide
  | legOfBlockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfForeignCurrencyStrategy => decide
  | blockTradeOfChainOfForwards => decide
  | blocktradeOfRollover => decide
  | crossingOfChainOfForwards => decide
  | sellAutoEntryOfChainOfForwards => decide
  | buyAutoEntryOfChainOfForwards => decide
  | swapBlockTrade => decide
  | swapBlockTradeWithContinuousCoupon => decide
  | blockTradeOfUnwind => decide
  | blockTradeOfSubstitution => decide
  | voiceOver => decide
  | firmOrder => decide
  | ipoCross => decide
  | unintentionalSelfCross => decide
  | withoutConcertation => decide
  | inavToClosingPriceTrading => decide
  | inavAfterClosing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfAgreement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfAgreement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfAgreement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfAgreement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfAgreement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfAgreement

/-- Indicator: one byte code -/
def Indicator.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Indicator where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ Indicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Indicator

def toByte : Indicator → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Indicator :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : Indicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Indicator) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Indicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Indicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Indicator) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Indicator) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Indicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Indicator

/-- Type Of Cross Trading: one byte code -/
def TypeOfCrossTrading.codes : List UInt8 :=
  [0x4F, 0x49]

inductive TypeOfCrossTrading where
  | preOpening -- Pre Opening
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TypeOfCrossTrading.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TypeOfCrossTrading

def toByte : TypeOfCrossTrading → UInt8
  | .preOpening => 0x4F
  | .intradayAuction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TypeOfCrossTrading :=
  if byte = 0x4F then .preOpening
  else .intradayAuction

def ofByte (byte : UInt8) : TypeOfCrossTrading :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TypeOfCrossTrading) : ofByte value.toByte = value := by
  cases value with
  | preOpening => decide
  | intradayAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TypeOfCrossTrading) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TypeOfCrossTrading × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TypeOfCrossTrading) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TypeOfCrossTrading) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TypeOfCrossTrading) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TypeOfCrossTrading

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

/-- Login Response Message: 1 bytes -/
structure LoginResponseMessage where
  loginResponseStatus : LoginResponseStatus
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  LoginResponseStatus.encode message.loginResponseStatus

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (loginResponseStatus, bytes) ← LoginResponseStatus.decode bytes
  pure ({ loginResponseStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginResponseStatus.encode_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginResponseStatus.decode_encode, some_bind]
  rfl

end LoginResponseMessage

/-- Replay Response Message: 8 bytes -/
structure ReplayResponseMessage where
  marketDataGroup : BitVec 8
  firstMessage : BitVec 32
  quantity : BitVec 16
  replayResponseStatus : ReplayResponseStatus
  deriving DecidableEq, Repr

namespace ReplayResponseMessage

def encode (message : ReplayResponseMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 4 message.firstMessage
    ++ (encodeUInt 2 message.quantity
    ++ (ReplayResponseStatus.encode message.replayResponseStatus)))

def decode (bytes : List UInt8) : Option (ReplayResponseMessage × List UInt8) := do
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (firstMessage, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 2 bytes
  let (replayResponseStatus, bytes) ← ReplayResponseStatus.decode bytes
  pure ({ marketDataGroup, firstMessage, quantity, replayResponseStatus }, bytes)

@[simp] theorem encode_length (message : ReplayResponseMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ReplayResponseStatus.encode_length]

theorem encode_length_pos (message : ReplayResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReplayResponseStatus.decode_encode, some_bind]
  rfl

end ReplayResponseMessage

/-- Snapshot Response Message: 6 bytes -/
structure SnapshotResponseMessage where
  quantityOfMessages : BitVec 32
  snapshotResponseStatus : SnapshotResponseStatus
  snapshotType : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotResponseMessage

def encode (message : SnapshotResponseMessage) : List UInt8 :=
  encodeUInt 4 message.quantityOfMessages
    ++ (SnapshotResponseStatus.encode message.snapshotResponseStatus
    ++ (encodeUInt 1 message.snapshotType))

def decode (bytes : List UInt8) : Option (SnapshotResponseMessage × List UInt8) := do
  let (quantityOfMessages, bytes) ← decodeUInt 4 bytes
  let (snapshotResponseStatus, bytes) ← SnapshotResponseStatus.decode bytes
  let (snapshotType, bytes) ← decodeUInt 1 bytes
  pure ({ quantityOfMessages, snapshotResponseStatus, snapshotType }, bytes)

@[simp] theorem encode_length (message : SnapshotResponseMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SnapshotResponseStatus.encode_length]

theorem encode_length_pos (message : SnapshotResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SnapshotResponseStatus.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotResponseMessage

/-- Snapshot Complete Message: 6 bytes -/
structure SnapshotCompleteMessage where
  sequenceNumber : BitVec 32
  marketDataGroup : BitVec 8
  snapshotType : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotCompleteMessage

def encode (message : SnapshotCompleteMessage) : List UInt8 :=
  encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 1 message.snapshotType))

def decode (bytes : List UInt8) : Option (SnapshotCompleteMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotType, bytes) ← decodeUInt 1 bytes
  pure ({ sequenceNumber, marketDataGroup, snapshotType }, bytes)

@[simp] theorem encode_length (message : SnapshotCompleteMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SnapshotCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotCompleteMessage

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

/-- Trade Cancellation Message: 8 bytes -/
structure TradeCancellationMessage where
  instrumentNumber : BitVec 32
  tradeNumber : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancellationMessage

def encode (message : TradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.tradeNumber)

def decode (bytes : List UInt8) : Option (TradeCancellationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, tradeNumber }, bytes)

@[simp] theorem encode_length (message : TradeCancellationMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCancellationMessage

/-- Status Changes Message: 5 bytes -/
structure StatusChangesMessage where
  instrumentNumber : BitVec 32
  instrumentStatus : InstrumentStatus
  deriving DecidableEq, Repr

namespace StatusChangesMessage

def encode (message : StatusChangesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (InstrumentStatus.encode message.instrumentStatus)

def decode (bytes : List UInt8) : Option (StatusChangesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (instrumentStatus, bytes) ← InstrumentStatus.decode bytes
  pure ({ instrumentNumber, instrumentStatus }, bytes)

@[simp] theorem encode_length (message : StatusChangesMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, InstrumentStatus.encode_length]

theorem encode_length_pos (message : StatusChangesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatusChangesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [InstrumentStatus.decode_encode, some_bind]
  rfl

end StatusChangesMessage

/-- Weighted Average Price Settlement Prices Message: 20 bytes -/
structure WeightedAveragePriceSettlementPricesMessage where
  instrumentNumber : BitVec 32
  weightedAveragePrice : BitVec 64
  volatility : BitVec 64
  deriving DecidableEq, Repr

namespace WeightedAveragePriceSettlementPricesMessage

def encode (message : WeightedAveragePriceSettlementPricesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.weightedAveragePrice
    ++ (encodeUInt 8 message.volatility))

def decode (bytes : List UInt8) : Option (WeightedAveragePriceSettlementPricesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (weightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (volatility, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, weightedAveragePrice, volatility }, bytes)

@[simp] theorem encode_length (message : WeightedAveragePriceSettlementPricesMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WeightedAveragePriceSettlementPricesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedAveragePriceSettlementPricesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WeightedAveragePriceSettlementPricesMessage

/-- Capital Trades Message: 51 bytes -/
structure CapitalTradesMessage where
  instrumentNumber : BitVec 32
  tradeTime : BitVec 64
  volumeInt324 : BitVec 32
  price : BitVec 64
  concertationType : ConcertationType
  tradeNumber : BitVec 32
  priceSetter : Alpha 1
  operationType : OperationType
  amount : BitVec 64
  buyAlpha5 : Alpha 5
  sellAlpha5 : Alpha 5
  settlement : Settlement
  auctionIndicator : AuctionIndicator
  deriving DecidableEq, Repr

namespace CapitalTradesMessage

def encode (message : CapitalTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.tradeTime
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.price
    ++ (ConcertationType.encode message.concertationType
    ++ (encodeUInt 4 message.tradeNumber
    ++ (Alpha.encode message.priceSetter
    ++ (OperationType.encode message.operationType
    ++ (encodeUInt 8 message.amount
    ++ (Alpha.encode message.buyAlpha5
    ++ (Alpha.encode message.sellAlpha5
    ++ (Settlement.encode message.settlement
    ++ (AuctionIndicator.encode message.auctionIndicator))))))))))))

def decode (bytes : List UInt8) : Option (CapitalTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (concertationType, bytes) ← ConcertationType.decode bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (priceSetter, bytes) ← Alpha.decode 1 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (buyAlpha5, bytes) ← Alpha.decode 5 bytes
  let (sellAlpha5, bytes) ← Alpha.decode 5 bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (auctionIndicator, bytes) ← AuctionIndicator.decode bytes
  pure ({ instrumentNumber, tradeTime, volumeInt324, price, concertationType, tradeNumber, priceSetter, operationType, amount, buyAlpha5, sellAlpha5, settlement, auctionIndicator }, bytes)

@[simp] theorem encode_length (message : CapitalTradesMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ConcertationType.encode_length, Alpha.encode_length, OperationType.encode_length, Settlement.encode_length, AuctionIndicator.encode_length]

theorem encode_length_pos (message : CapitalTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CapitalTradesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ConcertationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OperationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
  dsimp only
  rw [AuctionIndicator.decode_encode, some_bind]
  rfl

end CapitalTradesMessage

/-- Probable Allocation Price Message: 16 bytes -/
structure ProbableAllocationPriceMessage where
  instrumentNumber : BitVec 32
  probableAllocationPrice : BitVec 64
  volumeInt324 : BitVec 32
  deriving DecidableEq, Repr

namespace ProbableAllocationPriceMessage

def encode (message : ProbableAllocationPriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.probableAllocationPrice
    ++ (encodeUInt 4 message.volumeInt324))

def decode (bytes : List UInt8) : Option (ProbableAllocationPriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (probableAllocationPrice, bytes) ← decodeUInt 8 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, probableAllocationPrice, volumeInt324 }, bytes)

@[simp] theorem encode_length (message : ProbableAllocationPriceMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ProbableAllocationPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProbableAllocationPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ProbableAllocationPriceMessage

/-- Continuous Auctions Beginning Message: 20 bytes -/
structure ContinuousAuctionsBeginningMessage where
  instrumentNumber : BitVec 32
  beginningTimeOfAuction : BitVec 64
  endAuctionTime : BitVec 64
  deriving DecidableEq, Repr

namespace ContinuousAuctionsBeginningMessage

def encode (message : ContinuousAuctionsBeginningMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.beginningTimeOfAuction
    ++ (encodeUInt 8 message.endAuctionTime))

def decode (bytes : List UInt8) : Option (ContinuousAuctionsBeginningMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (beginningTimeOfAuction, bytes) ← decodeUInt 8 bytes
  let (endAuctionTime, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, beginningTimeOfAuction, endAuctionTime }, bytes)

@[simp] theorem encode_length (message : ContinuousAuctionsBeginningMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ContinuousAuctionsBeginningMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ContinuousAuctionsBeginningMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ContinuousAuctionsBeginningMessage

/-- Middle Price Existing Quotes Message: 5 bytes -/
structure MiddlePriceExistingQuotesMessage where
  instrumentNumber : BitVec 32
  existingPostures : Alpha 1
  deriving DecidableEq, Repr

namespace MiddlePriceExistingQuotesMessage

def encode (message : MiddlePriceExistingQuotesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Alpha.encode message.existingPostures)

def decode (bytes : List UInt8) : Option (MiddlePriceExistingQuotesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (existingPostures, bytes) ← Alpha.decode 1 bytes
  pure ({ instrumentNumber, existingPostures }, bytes)

@[simp] theorem encode_length (message : MiddlePriceExistingQuotesMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MiddlePriceExistingQuotesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MiddlePriceExistingQuotesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MiddlePriceExistingQuotesMessage

/-- Registry Operations Message: 61 bytes -/
structure RegistryOperationsMessage where
  instrumentNumber : BitVec 32
  offerType : OfferType
  income : Income
  valueType : Alpha 4
  issuer : Alpha 7
  series : Alpha 6
  maximumVolume : BitVec 64
  registeredVolume : BitVec 64
  priceRate : BitVec 64
  settlementDate : BitVec 64
  firm : Alpha 5
  movement : Movement
  deriving DecidableEq, Repr

namespace RegistryOperationsMessage

def encode (message : RegistryOperationsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (OfferType.encode message.offerType
    ++ (Income.encode message.income
    ++ (Alpha.encode message.valueType
    ++ (Alpha.encode message.issuer
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.maximumVolume
    ++ (encodeUInt 8 message.registeredVolume
    ++ (encodeUInt 8 message.priceRate
    ++ (encodeUInt 8 message.settlementDate
    ++ (Alpha.encode message.firm
    ++ (Movement.encode message.movement)))))))))))

def decode (bytes : List UInt8) : Option (RegistryOperationsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (offerType, bytes) ← OfferType.decode bytes
  let (income, bytes) ← Income.decode bytes
  let (valueType, bytes) ← Alpha.decode 4 bytes
  let (issuer, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (maximumVolume, bytes) ← decodeUInt 8 bytes
  let (registeredVolume, bytes) ← decodeUInt 8 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (settlementDate, bytes) ← decodeUInt 8 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  let (movement, bytes) ← Movement.decode bytes
  pure ({ instrumentNumber, offerType, income, valueType, issuer, series, maximumVolume, registeredVolume, priceRate, settlementDate, firm, movement }, bytes)

@[simp] theorem encode_length (message : RegistryOperationsMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OfferType.encode_length, Income.encode_length, Alpha.encode_length, Movement.encode_length]

theorem encode_length_pos (message : RegistryOperationsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegistryOperationsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OfferType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Income.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Movement.decode_encode, some_bind]
  rfl

end RegistryOperationsMessage

/-- Mutual Fund Trades Message: 52 bytes -/
structure MutualFundTradesMessage where
  instrumentNumber : BitVec 32
  tradeDate : BitVec 64
  price : BitVec 64
  bookValue : BitVec 64
  numberOfSalesTransactions : BitVec 32
  salesVolume : BitVec 64
  numberOfBuyTransactions : BitVec 32
  buyVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MutualFundTradesMessage

def encode (message : MutualFundTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.tradeDate
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.bookValue
    ++ (encodeUInt 4 message.numberOfSalesTransactions
    ++ (encodeUInt 8 message.salesVolume
    ++ (encodeUInt 4 message.numberOfBuyTransactions
    ++ (encodeUInt 8 message.buyVolume)))))))

def decode (bytes : List UInt8) : Option (MutualFundTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeDate, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (bookValue, bytes) ← decodeUInt 8 bytes
  let (numberOfSalesTransactions, bytes) ← decodeUInt 4 bytes
  let (salesVolume, bytes) ← decodeUInt 8 bytes
  let (numberOfBuyTransactions, bytes) ← decodeUInt 4 bytes
  let (buyVolume, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, tradeDate, price, bookValue, numberOfSalesTransactions, salesVolume, numberOfBuyTransactions, buyVolume }, bytes)

@[simp] theorem encode_length (message : MutualFundTradesMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : MutualFundTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MutualFundTradesMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MutualFundTradesMessage

/-- Tradability Message: 64 bytes -/
structure TradabilityMessage where
  instrumentNumber : BitVec 32
  numberOfOperations : BitVec 32
  volumeInt648 : BitVec 64
  amount : BitVec 64
  openingPrice : BitVec 64
  maximum : BitVec 64
  minimum : BitVec 64
  average : BitVec 64
  last : BitVec 64
  deriving DecidableEq, Repr

namespace TradabilityMessage

def encode (message : TradabilityMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.numberOfOperations
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.amount
    ++ (encodeUInt 8 message.openingPrice
    ++ (encodeUInt 8 message.maximum
    ++ (encodeUInt 8 message.minimum
    ++ (encodeUInt 8 message.average
    ++ (encodeUInt 8 message.last))))))))

def decode (bytes : List UInt8) : Option (TradabilityMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (numberOfOperations, bytes) ← decodeUInt 4 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (openingPrice, bytes) ← decodeUInt 8 bytes
  let (maximum, bytes) ← decodeUInt 8 bytes
  let (minimum, bytes) ← decodeUInt 8 bytes
  let (average, bytes) ← decodeUInt 8 bytes
  let (last, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, numberOfOperations, volumeInt648, amount, openingPrice, maximum, minimum, average, last }, bytes)

@[simp] theorem encode_length (message : TradabilityMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradabilityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradabilityMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradabilityMessage

/-- Virtual Trades Message: 25 bytes -/
structure VirtualTradesMessage where
  instrumentNumber : BitVec 32
  virtualTradesStatus : VirtualTradesStatus
  operationType : OperationType
  number : BitVec 32
  volumeInt324 : BitVec 32
  concertation : Concertation
  buyAlpha5 : Alpha 5
  sellAlpha5 : Alpha 5
  deriving DecidableEq, Repr

namespace VirtualTradesMessage

def encode (message : VirtualTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (VirtualTradesStatus.encode message.virtualTradesStatus
    ++ (OperationType.encode message.operationType
    ++ (encodeUInt 4 message.number
    ++ (encodeUInt 4 message.volumeInt324
    ++ (Concertation.encode message.concertation
    ++ (Alpha.encode message.buyAlpha5
    ++ (Alpha.encode message.sellAlpha5)))))))

def decode (bytes : List UInt8) : Option (VirtualTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (virtualTradesStatus, bytes) ← VirtualTradesStatus.decode bytes
  let (operationType, bytes) ← OperationType.decode bytes
  let (number, bytes) ← decodeUInt 4 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (concertation, bytes) ← Concertation.decode bytes
  let (buyAlpha5, bytes) ← Alpha.decode 5 bytes
  let (sellAlpha5, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, virtualTradesStatus, operationType, number, volumeInt324, concertation, buyAlpha5, sellAlpha5 }, bytes)

@[simp] theorem encode_length (message : VirtualTradesMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, VirtualTradesStatus.encode_length, OperationType.encode_length, Concertation.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : VirtualTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VirtualTradesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, VirtualTradesStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OperationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Concertation.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end VirtualTradesMessage

/-- Order Addition Message: 34 bytes -/
structure OrderAdditionMessage where
  instrumentNumber : BitVec 32
  dateAndTime : BitVec 64
  number : BitVec 32
  direction : Direction
  volumeInt324 : BitVec 32
  price : BitVec 64
  participant : Alpha 5
  deriving DecidableEq, Repr

namespace OrderAdditionMessage

def encode (message : OrderAdditionMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.dateAndTime
    ++ (encodeUInt 4 message.number
    ++ (Direction.encode message.direction
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.participant))))))

def decode (bytes : List UInt8) : Option (OrderAdditionMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (dateAndTime, bytes) ← decodeUInt 8 bytes
  let (number, bytes) ← decodeUInt 4 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, dateAndTime, number, direction, volumeInt324, price, participant }, bytes)

@[simp] theorem encode_length (message : OrderAdditionMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Direction.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderAdditionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdditionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAdditionMessage

/-- Execution Of Orders Message: 32 bytes -/
structure ExecutionOfOrdersMessage where
  instrumentNumber : BitVec 32
  date : BitVec 64
  number : BitVec 32
  volumeInt324 : BitVec 32
  tradeNumber : BitVec 32
  executionPrice : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionOfOrdersMessage

def encode (message : ExecutionOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 4 message.number
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 4 message.tradeNumber
    ++ (encodeUInt 8 message.executionPrice)))))

def decode (bytes : List UInt8) : Option (ExecutionOfOrdersMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (number, bytes) ← decodeUInt 4 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, date, number, volumeInt324, tradeNumber, executionPrice }, bytes)

@[simp] theorem encode_length (message : ExecutionOfOrdersMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ExecutionOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionOfOrdersMessage) (rest : List UInt8) :
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

end ExecutionOfOrdersMessage

/-- Order Cancellation Message: 16 bytes -/
structure OrderCancellationMessage where
  instrumentNumber : BitVec 32
  date : BitVec 64
  number : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancellationMessage

def encode (message : OrderCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 4 message.number))

def decode (bytes : List UInt8) : Option (OrderCancellationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (number, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, date, number }, bytes)

@[simp] theorem encode_length (message : OrderCancellationMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancellationMessage

/-- Order Change Message: 41 bytes -/
structure OrderChangeMessage where
  instrumentNumber : BitVec 32
  originalDate : BitVec 64
  originalNumber : BitVec 32
  newDate : BitVec 64
  newNumber : BitVec 32
  direction : Direction
  volumeInt324 : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderChangeMessage

def encode (message : OrderChangeMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.originalDate
    ++ (encodeUInt 4 message.originalNumber
    ++ (encodeUInt 8 message.newDate
    ++ (encodeUInt 4 message.newNumber
    ++ (Direction.encode message.direction
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.price)))))))

def decode (bytes : List UInt8) : Option (OrderChangeMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (originalDate, bytes) ← decodeUInt 8 bytes
  let (originalNumber, bytes) ← decodeUInt 4 bytes
  let (newDate, bytes) ← decodeUInt 8 bytes
  let (newNumber, bytes) ← decodeUInt 4 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, originalDate, originalNumber, newDate, newNumber, direction, volumeInt324, price }, bytes)

@[simp] theorem encode_length (message : OrderChangeMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Direction.encode_length]

theorem encode_length_pos (message : OrderChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderChangeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderChangeMessage

/-- Price Level: 14 bytes -/
structure PriceLevel where
  price : BitVec 64
  numberOfOrders : BitVec 16
  volumeInt324 : BitVec 32
  deriving DecidableEq, Repr

namespace PriceLevel

def encode (message : PriceLevel) : List UInt8 :=
  encodeUInt 8 message.price
    ++ (encodeUInt 2 message.numberOfOrders
    ++ (encodeUInt 4 message.volumeInt324))

def decode (bytes : List UInt8) : Option (PriceLevel × List UInt8) := do
  let (price, bytes) ← decodeUInt 8 bytes
  let (numberOfOrders, bytes) ← decodeUInt 2 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  pure ({ price, numberOfOrders, volumeInt324 }, bytes)

@[simp] theorem encode_length (message : PriceLevel) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PriceLevel

/-- Depth Message -/
structure DepthMessage where
  instrumentNumber : BitVec 32
  side : BitVec 8
  priceLevel : Bounded 1 PriceLevel
  deriving DecidableEq, Repr

namespace DepthMessage

def encode (message : DepthMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.priceLevel.val.length)
    ++ (encodeMany PriceLevel.encode message.priceLevel.val)))

def decode (bytes : List UInt8) : Option (DepthMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (purchaseOrSaleLevels, bytes) ← decodeUInt 1 bytes
  let (priceLevel_, bytes) ← decodeMany PriceLevel.decode purchaseOrSaleLevels.toNat bytes
  if fits_priceLevel : priceLevel_.length < 256 ^ 1 then
    pure ({ instrumentNumber, side, priceLevel := ⟨priceLevel_, fits_priceLevel⟩ }, bytes)
  else none

theorem encode_length_pos (message : DepthMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DepthMessage) : (encode message).length ≤ 3576 := by
  have bound_priceLevel := message.priceLevel.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const PriceLevel.encode 14 PriceLevel.encode_length]
  omega

@[simp] theorem decode_encode (message : DepthMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PriceLevel.encode PriceLevel.decode PriceLevel.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.priceLevel.length_lt]
  rfl

end DepthMessage

/-- Best Offer Message: 18 bytes -/
structure BestOfferMessage where
  instrumentNumber : BitVec 32
  volumeInt324 : BitVec 32
  priceRate : BitVec 64
  offerDirection : OfferDirection
  operationType : OperationType
  deriving DecidableEq, Repr

namespace BestOfferMessage

def encode (message : BestOfferMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.priceRate
    ++ (OfferDirection.encode message.offerDirection
    ++ (OperationType.encode message.operationType))))

def decode (bytes : List UInt8) : Option (BestOfferMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (offerDirection, bytes) ← OfferDirection.decode bytes
  let (operationType, bytes) ← OperationType.decode bytes
  pure ({ instrumentNumber, volumeInt324, priceRate, offerDirection, operationType }, bytes)

@[simp] theorem encode_length (message : BestOfferMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OfferDirection.encode_length, OperationType.encode_length]

theorem encode_length_pos (message : BestOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OfferDirection.decode_encode, some_bind]
  dsimp only
  rw [OperationType.decode_encode, some_bind]
  rfl

end BestOfferMessage

/-- Public Offerings Message: 66 bytes -/
structure PublicOfferingsMessage where
  instrumentNumber : BitVec 32
  number : BitVec 32
  volumeInt648 : BitVec 64
  discountRateOrPrice : BitVec 64
  rateOfReturn : BitVec 32
  termDays : BitVec 16
  currencyType : CurrencyType
  settlement : Settlement
  buyAlpha5 : Alpha 5
  sellAlpha5 : Alpha 5
  placementDate : BitVec 64
  issueDate : BitVec 64
  maturityDate : BitVec 64
  deriving DecidableEq, Repr

namespace PublicOfferingsMessage

def encode (message : PublicOfferingsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.number
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.discountRateOrPrice
    ++ (encodeUInt 4 message.rateOfReturn
    ++ (encodeUInt 2 message.termDays
    ++ (CurrencyType.encode message.currencyType
    ++ (Settlement.encode message.settlement
    ++ (Alpha.encode message.buyAlpha5
    ++ (Alpha.encode message.sellAlpha5
    ++ (encodeUInt 8 message.placementDate
    ++ (encodeUInt 8 message.issueDate
    ++ (encodeUInt 8 message.maturityDate))))))))))))

def decode (bytes : List UInt8) : Option (PublicOfferingsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (number, bytes) ← decodeUInt 4 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (discountRateOrPrice, bytes) ← decodeUInt 8 bytes
  let (rateOfReturn, bytes) ← decodeUInt 4 bytes
  let (termDays, bytes) ← decodeUInt 2 bytes
  let (currencyType, bytes) ← CurrencyType.decode bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (buyAlpha5, bytes) ← Alpha.decode 5 bytes
  let (sellAlpha5, bytes) ← Alpha.decode 5 bytes
  let (placementDate, bytes) ← decodeUInt 8 bytes
  let (issueDate, bytes) ← decodeUInt 8 bytes
  let (maturityDate, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, number, volumeInt648, discountRateOrPrice, rateOfReturn, termDays, currencyType, settlement, buyAlpha5, sellAlpha5, placementDate, issueDate, maturityDate }, bytes)

@[simp] theorem encode_length (message : PublicOfferingsMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CurrencyType.encode_length, Settlement.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : PublicOfferingsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PublicOfferingsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CurrencyType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PublicOfferingsMessage

/-- Open Interest Message: 8 bytes -/
structure OpenInterestMessage where
  instrumentNumber : BitVec 32
  openInterest : BitVec 32
  deriving DecidableEq, Repr

namespace OpenInterestMessage

def encode (message : OpenInterestMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 4 message.openInterest)

def decode (bytes : List UInt8) : Option (OpenInterestMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (openInterest, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, openInterest }, bytes)

@[simp] theorem encode_length (message : OpenInterestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OpenInterestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpenInterestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpenInterestMessage

/-- Derivatives Market Trades Message: 43 bytes -/
structure DerivativesMarketTradesMessage where
  instrumentNumber : BitVec 32
  tradeTime : BitVec 64
  volumeInt324 : BitVec 32
  priceRate : BitVec 64
  concertationType : ConcertationType
  tradeNumber : BitVec 32
  operationType : OperationType
  amount : BitVec 64
  parentTradeNumber : BitVec 32
  legType : LegType
  deriving DecidableEq, Repr

namespace DerivativesMarketTradesMessage

def encode (message : DerivativesMarketTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.tradeTime
    ++ (encodeUInt 4 message.volumeInt324
    ++ (encodeUInt 8 message.priceRate
    ++ (ConcertationType.encode message.concertationType
    ++ (encodeUInt 4 message.tradeNumber
    ++ (OperationType.encode message.operationType
    ++ (encodeUInt 8 message.amount
    ++ (encodeUInt 4 message.parentTradeNumber
    ++ (LegType.encode message.legType)))))))))

def decode (bytes : List UInt8) : Option (DerivativesMarketTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (tradeTime, bytes) ← decodeUInt 8 bytes
  let (volumeInt324, bytes) ← decodeUInt 4 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (concertationType, bytes) ← ConcertationType.decode bytes
  let (tradeNumber, bytes) ← decodeUInt 4 bytes
  let (operationType, bytes) ← OperationType.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (parentTradeNumber, bytes) ← decodeUInt 4 bytes
  let (legType, bytes) ← LegType.decode bytes
  pure ({ instrumentNumber, tradeTime, volumeInt324, priceRate, concertationType, tradeNumber, operationType, amount, parentTradeNumber, legType }, bytes)

@[simp] theorem encode_length (message : DerivativesMarketTradesMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ConcertationType.encode_length, OperationType.encode_length, LegType.encode_length]

theorem encode_length_pos (message : DerivativesMarketTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DerivativesMarketTradesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ConcertationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OperationType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [LegType.decode_encode, some_bind]
  rfl

end DerivativesMarketTradesMessage

/-- Statistics Of Instruments Message: 44 bytes -/
structure StatisticsOfInstrumentsMessage where
  instrumentNumber : BitVec 32
  previousSettlementPrice : BitVec 64
  openingPrice : BitVec 64
  maxPriceOfTheDay : BitVec 64
  lowerPriceOfTheDay : BitVec 64
  lastPriceOfTheDay : BitVec 64
  deriving DecidableEq, Repr

namespace StatisticsOfInstrumentsMessage

def encode (message : StatisticsOfInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.previousSettlementPrice
    ++ (encodeUInt 8 message.openingPrice
    ++ (encodeUInt 8 message.maxPriceOfTheDay
    ++ (encodeUInt 8 message.lowerPriceOfTheDay
    ++ (encodeUInt 8 message.lastPriceOfTheDay)))))

def decode (bytes : List UInt8) : Option (StatisticsOfInstrumentsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (previousSettlementPrice, bytes) ← decodeUInt 8 bytes
  let (openingPrice, bytes) ← decodeUInt 8 bytes
  let (maxPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  let (lowerPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  let (lastPriceOfTheDay, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, previousSettlementPrice, openingPrice, maxPriceOfTheDay, lowerPriceOfTheDay, lastPriceOfTheDay }, bytes)

@[simp] theorem encode_length (message : StatisticsOfInstrumentsMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StatisticsOfInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatisticsOfInstrumentsMessage) (rest : List UInt8) :
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

end StatisticsOfInstrumentsMessage

/-- General Indices Message: 33 bytes -/
structure GeneralIndicesMessage where
  component : Alpha 2
  sector : BitVec 8
  indicesHour : BitVec 64
  volumeInt648 : BitVec 64
  indicesPrice44 : BitVec 32
  variation : BitVec 32
  percentage : BitVec 32
  trend : Trend
  indicesStatus : IndicesStatus
  deriving DecidableEq, Repr

namespace GeneralIndicesMessage

def encode (message : GeneralIndicesMessage) : List UInt8 :=
  Alpha.encode message.component
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 8 message.indicesHour
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 4 message.indicesPrice44
    ++ (encodeUInt 4 message.variation
    ++ (encodeUInt 4 message.percentage
    ++ (Trend.encode message.trend
    ++ (IndicesStatus.encode message.indicesStatus))))))))

def decode (bytes : List UInt8) : Option (GeneralIndicesMessage × List UInt8) := do
  let (component, bytes) ← Alpha.decode 2 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (indicesHour, bytes) ← decodeUInt 8 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (indicesPrice44, bytes) ← decodeUInt 4 bytes
  let (variation, bytes) ← decodeUInt 4 bytes
  let (percentage, bytes) ← decodeUInt 4 bytes
  let (trend, bytes) ← Trend.decode bytes
  let (indicesStatus, bytes) ← IndicesStatus.decode bytes
  pure ({ component, sector, indicesHour, volumeInt648, indicesPrice44, variation, percentage, trend, indicesStatus }, bytes)

@[simp] theorem encode_length (message : GeneralIndicesMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Trend.encode_length, IndicesStatus.encode_length]

theorem encode_length_pos (message : GeneralIndicesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GeneralIndicesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Trend.decode_encode, some_bind]
  dsimp only
  rw [IndicesStatus.decode_encode, some_bind]
  rfl

end GeneralIndicesMessage

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

/-- Inav Message: 12 bytes -/
structure InavMessage where
  tracNumber : BitVec 32
  theoreticalCurrentPrice : BitVec 64
  deriving DecidableEq, Repr

namespace InavMessage

def encode (message : InavMessage) : List UInt8 :=
  encodeUInt 4 message.tracNumber
    ++ (encodeUInt 8 message.theoreticalCurrentPrice)

def decode (bytes : List UInt8) : Option (InavMessage × List UInt8) := do
  let (tracNumber, bytes) ← decodeUInt 4 bytes
  let (theoreticalCurrentPrice, bytes) ← decodeUInt 8 bytes
  pure ({ tracNumber, theoreticalCurrentPrice }, bytes)

@[simp] theorem encode_length (message : InavMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : InavMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InavMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InavMessage

/-- Dollar Buy Sell Message: 38 bytes -/
structure DollarBuySellMessage where
  postureDate : BitVec 64
  currency : Alpha 5
  dollarSide : Alpha 1
  buyPrecio88 : BitVec 64
  sellPrecio88 : BitVec 64
  lastDeal : BitVec 64
  deriving DecidableEq, Repr

namespace DollarBuySellMessage

def encode (message : DollarBuySellMessage) : List UInt8 :=
  encodeUInt 8 message.postureDate
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.dollarSide
    ++ (encodeUInt 8 message.buyPrecio88
    ++ (encodeUInt 8 message.sellPrecio88
    ++ (encodeUInt 8 message.lastDeal)))))

def decode (bytes : List UInt8) : Option (DollarBuySellMessage × List UInt8) := do
  let (postureDate, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 5 bytes
  let (dollarSide, bytes) ← Alpha.decode 1 bytes
  let (buyPrecio88, bytes) ← decodeUInt 8 bytes
  let (sellPrecio88, bytes) ← decodeUInt 8 bytes
  let (lastDeal, bytes) ← decodeUInt 8 bytes
  pure ({ postureDate, currency, dollarSide, buyPrecio88, sellPrecio88, lastDeal }, bytes)

@[simp] theorem encode_length (message : DollarBuySellMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : DollarBuySellMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DollarBuySellMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DollarBuySellMessage

/-- Short Sales Balances Per Instrument Message: 44 bytes -/
structure ShortSalesBalancesPerInstrumentMessage where
  instrumentNumber : BitVec 32
  date : BitVec 64
  previousBalance : BitVec 64
  amountTraded : BitVec 64
  buybacks : BitVec 64
  currentBalance : BitVec 64
  deriving DecidableEq, Repr

namespace ShortSalesBalancesPerInstrumentMessage

def encode (message : ShortSalesBalancesPerInstrumentMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.previousBalance
    ++ (encodeUInt 8 message.amountTraded
    ++ (encodeUInt 8 message.buybacks
    ++ (encodeUInt 8 message.currentBalance)))))

def decode (bytes : List UInt8) : Option (ShortSalesBalancesPerInstrumentMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (previousBalance, bytes) ← decodeUInt 8 bytes
  let (amountTraded, bytes) ← decodeUInt 8 bytes
  let (buybacks, bytes) ← decodeUInt 8 bytes
  let (currentBalance, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, date, previousBalance, amountTraded, buybacks, currentBalance }, bytes)

@[simp] theorem encode_length (message : ShortSalesBalancesPerInstrumentMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ShortSalesBalancesPerInstrumentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShortSalesBalancesPerInstrumentMessage) (rest : List UInt8) :
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

end ShortSalesBalancesPerInstrumentMessage

/-- Capital Market Multiples Message: 130 bytes -/
structure CapitalMarketMultiplesMessage where
  instrumentId : BitVec 32
  multipleType : MultipleType
  registryNumber : Alpha 1
  sector : BitVec 8
  subsector : BitVec 8
  businessLine : BitVec 8
  subLine : BitVec 8
  pflepaMultiple : BitVec 64
  pfepaMultiple : BitVec 64
  veUaiidaMultiple : BitVec 64
  pU : BitVec 64
  pVl : BitVec 64
  f1PUnoc : BitVec 64
  f2PUnoc : BitVec 64
  f1PUe : BitVec 64
  f2PUe : BitVec 64
  f1VeUaiida : BitVec 64
  f2VeUaiida : BitVec 64
  f1PU : BitVec 64
  f2PU : BitVec 64
  f1PVl : BitVec 64
  f2PVl : BitVec 64
  deriving DecidableEq, Repr

namespace CapitalMarketMultiplesMessage

def encode (message : CapitalMarketMultiplesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentId
    ++ (MultipleType.encode message.multipleType
    ++ (Alpha.encode message.registryNumber
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 1 message.subsector
    ++ (encodeUInt 1 message.businessLine
    ++ (encodeUInt 1 message.subLine
    ++ (encodeUInt 8 message.pflepaMultiple
    ++ (encodeUInt 8 message.pfepaMultiple
    ++ (encodeUInt 8 message.veUaiidaMultiple
    ++ (encodeUInt 8 message.pU
    ++ (encodeUInt 8 message.pVl
    ++ (encodeUInt 8 message.f1PUnoc
    ++ (encodeUInt 8 message.f2PUnoc
    ++ (encodeUInt 8 message.f1PUe
    ++ (encodeUInt 8 message.f2PUe
    ++ (encodeUInt 8 message.f1VeUaiida
    ++ (encodeUInt 8 message.f2VeUaiida
    ++ (encodeUInt 8 message.f1PU
    ++ (encodeUInt 8 message.f2PU
    ++ (encodeUInt 8 message.f1PVl
    ++ (encodeUInt 8 message.f2PVl)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (CapitalMarketMultiplesMessage × List UInt8) := do
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (multipleType, bytes) ← MultipleType.decode bytes
  let (registryNumber, bytes) ← Alpha.decode 1 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (subsector, bytes) ← decodeUInt 1 bytes
  let (businessLine, bytes) ← decodeUInt 1 bytes
  let (subLine, bytes) ← decodeUInt 1 bytes
  let (pflepaMultiple, bytes) ← decodeUInt 8 bytes
  let (pfepaMultiple, bytes) ← decodeUInt 8 bytes
  let (veUaiidaMultiple, bytes) ← decodeUInt 8 bytes
  let (pU, bytes) ← decodeUInt 8 bytes
  let (pVl, bytes) ← decodeUInt 8 bytes
  let (f1PUnoc, bytes) ← decodeUInt 8 bytes
  let (f2PUnoc, bytes) ← decodeUInt 8 bytes
  let (f1PUe, bytes) ← decodeUInt 8 bytes
  let (f2PUe, bytes) ← decodeUInt 8 bytes
  let (f1VeUaiida, bytes) ← decodeUInt 8 bytes
  let (f2VeUaiida, bytes) ← decodeUInt 8 bytes
  let (f1PU, bytes) ← decodeUInt 8 bytes
  let (f2PU, bytes) ← decodeUInt 8 bytes
  let (f1PVl, bytes) ← decodeUInt 8 bytes
  let (f2PVl, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentId, multipleType, registryNumber, sector, subsector, businessLine, subLine, pflepaMultiple, pfepaMultiple, veUaiidaMultiple, pU, pVl, f1PUnoc, f2PUnoc, f1PUe, f2PUe, f1VeUaiida, f2VeUaiida, f1PU, f2PU, f1PVl, f2PVl }, bytes)

@[simp] theorem encode_length (message : CapitalMarketMultiplesMessage) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, MultipleType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CapitalMarketMultiplesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CapitalMarketMultiplesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MultipleType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CapitalMarketMultiplesMessage

/-- Benchmark Message: 149 bytes -/
structure BenchmarkMessage where
  benchmarkName : Alpha 40
  benchmarkDate : BitVec 64
  outstanding : BitVec 64
  integerAmount : BitVec 64
  decimalAmount : BitVec 32
  indicesPrecio88 : BitVec 64
  indices24 : BitVec 64
  rebalance : Rebalance
  dailyPerformance : BitVec 64
  annualPerformance : BitVec 64
  monthlyPerformance : BitVec 64
  last12MonthsPerformance : BitVec 64
  t24HoursDailyPerformance : BitVec 64
  t24HoursAnnualPerformance : BitVec 64
  t24HoursMonthlyPerformance : BitVec 64
  last12Months24HoursPerformance : BitVec 64
  deriving DecidableEq, Repr

namespace BenchmarkMessage

def encode (message : BenchmarkMessage) : List UInt8 :=
  Alpha.encode message.benchmarkName
    ++ (encodeUInt 8 message.benchmarkDate
    ++ (encodeUInt 8 message.outstanding
    ++ (encodeUInt 8 message.integerAmount
    ++ (encodeUInt 4 message.decimalAmount
    ++ (encodeUInt 8 message.indicesPrecio88
    ++ (encodeUInt 8 message.indices24
    ++ (Rebalance.encode message.rebalance
    ++ (encodeUInt 8 message.dailyPerformance
    ++ (encodeUInt 8 message.annualPerformance
    ++ (encodeUInt 8 message.monthlyPerformance
    ++ (encodeUInt 8 message.last12MonthsPerformance
    ++ (encodeUInt 8 message.t24HoursDailyPerformance
    ++ (encodeUInt 8 message.t24HoursAnnualPerformance
    ++ (encodeUInt 8 message.t24HoursMonthlyPerformance
    ++ (encodeUInt 8 message.last12Months24HoursPerformance)))))))))))))))

def decode (bytes : List UInt8) : Option (BenchmarkMessage × List UInt8) := do
  let (benchmarkName, bytes) ← Alpha.decode 40 bytes
  let (benchmarkDate, bytes) ← decodeUInt 8 bytes
  let (outstanding, bytes) ← decodeUInt 8 bytes
  let (integerAmount, bytes) ← decodeUInt 8 bytes
  let (decimalAmount, bytes) ← decodeUInt 4 bytes
  let (indicesPrecio88, bytes) ← decodeUInt 8 bytes
  let (indices24, bytes) ← decodeUInt 8 bytes
  let (rebalance, bytes) ← Rebalance.decode bytes
  let (dailyPerformance, bytes) ← decodeUInt 8 bytes
  let (annualPerformance, bytes) ← decodeUInt 8 bytes
  let (monthlyPerformance, bytes) ← decodeUInt 8 bytes
  let (last12MonthsPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursDailyPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursAnnualPerformance, bytes) ← decodeUInt 8 bytes
  let (t24HoursMonthlyPerformance, bytes) ← decodeUInt 8 bytes
  let (last12Months24HoursPerformance, bytes) ← decodeUInt 8 bytes
  pure ({ benchmarkName, benchmarkDate, outstanding, integerAmount, decimalAmount, indicesPrecio88, indices24, rebalance, dailyPerformance, annualPerformance, monthlyPerformance, last12MonthsPerformance, t24HoursDailyPerformance, t24HoursAnnualPerformance, t24HoursMonthlyPerformance, last12Months24HoursPerformance }, bytes)

@[simp] theorem encode_length (message : BenchmarkMessage) : (encode message).length = 149 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Rebalance.encode_length]

theorem encode_length_pos (message : BenchmarkMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BenchmarkMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Rebalance.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

end BenchmarkMessage

/-- Capitalization Rules Message: 39 bytes -/
structure CapitalizationRulesMessage where
  instrumentNumber : BitVec 32
  dateIndicators : BitVec 64
  bursatilityIndices : BitVec 32
  bursatilityIndicesSign : BursatilityIndicesSign
  betaCoefficient : BitVec 64
  betaCoefficientSign : BetaCoefficientSign
  correlationCoefficient : BitVec 64
  correlationCoefficientSign : CorrelationCoefficientSign
  deltaDifference : BitVec 32
  deriving DecidableEq, Repr

namespace CapitalizationRulesMessage

def encode (message : CapitalizationRulesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.dateIndicators
    ++ (encodeUInt 4 message.bursatilityIndices
    ++ (BursatilityIndicesSign.encode message.bursatilityIndicesSign
    ++ (encodeUInt 8 message.betaCoefficient
    ++ (BetaCoefficientSign.encode message.betaCoefficientSign
    ++ (encodeUInt 8 message.correlationCoefficient
    ++ (CorrelationCoefficientSign.encode message.correlationCoefficientSign
    ++ (encodeUInt 4 message.deltaDifference))))))))

def decode (bytes : List UInt8) : Option (CapitalizationRulesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (dateIndicators, bytes) ← decodeUInt 8 bytes
  let (bursatilityIndices, bytes) ← decodeUInt 4 bytes
  let (bursatilityIndicesSign, bytes) ← BursatilityIndicesSign.decode bytes
  let (betaCoefficient, bytes) ← decodeUInt 8 bytes
  let (betaCoefficientSign, bytes) ← BetaCoefficientSign.decode bytes
  let (correlationCoefficient, bytes) ← decodeUInt 8 bytes
  let (correlationCoefficientSign, bytes) ← CorrelationCoefficientSign.decode bytes
  let (deltaDifference, bytes) ← decodeUInt 4 bytes
  pure ({ instrumentNumber, dateIndicators, bursatilityIndices, bursatilityIndicesSign, betaCoefficient, betaCoefficientSign, correlationCoefficient, correlationCoefficientSign, deltaDifference }, bytes)

@[simp] theorem encode_length (message : CapitalizationRulesMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BursatilityIndicesSign.encode_length, BetaCoefficientSign.encode_length, CorrelationCoefficientSign.encode_length]

theorem encode_length_pos (message : CapitalizationRulesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CapitalizationRulesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BursatilityIndicesSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BetaCoefficientSign.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrelationCoefficientSign.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CapitalizationRulesMessage

/-- Closing Price Origin Message: 13 bytes -/
structure ClosingPriceOriginMessage where
  instrumentNumber : BitVec 32
  originPrice : BitVec 64
  sending : Sending
  deriving DecidableEq, Repr

namespace ClosingPriceOriginMessage

def encode (message : ClosingPriceOriginMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (encodeUInt 8 message.originPrice
    ++ (Sending.encode message.sending))

def decode (bytes : List UInt8) : Option (ClosingPriceOriginMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (originPrice, bytes) ← decodeUInt 8 bytes
  let (sending, bytes) ← Sending.decode bytes
  pure ({ instrumentNumber, originPrice, sending }, bytes)

@[simp] theorem encode_length (message : ClosingPriceOriginMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Sending.encode_length]

theorem encode_length_pos (message : ClosingPriceOriginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClosingPriceOriginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Sending.decode_encode, some_bind]
  rfl

end ClosingPriceOriginMessage

/-- Mutual Funds Trades Message: 53 bytes -/
structure MutualFundsTradesMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  dateOfTheTrade : BitVec 64
  price : BitVec 64
  bookValue : BitVec 64
  numberOfSalesTrades : BitVec 32
  salesVolume : BitVec 64
  numberOfPurchaseTrades : BitVec 32
  purchaseVolume : BitVec 64
  deriving DecidableEq, Repr

namespace MutualFundsTradesMessage

def encode (message : MutualFundsTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.dateOfTheTrade
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.bookValue
    ++ (encodeUInt 4 message.numberOfSalesTrades
    ++ (encodeUInt 8 message.salesVolume
    ++ (encodeUInt 4 message.numberOfPurchaseTrades
    ++ (encodeUInt 8 message.purchaseVolume))))))))

def decode (bytes : List UInt8) : Option (MutualFundsTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (dateOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (bookValue, bytes) ← decodeUInt 8 bytes
  let (numberOfSalesTrades, bytes) ← decodeUInt 4 bytes
  let (salesVolume, bytes) ← decodeUInt 8 bytes
  let (numberOfPurchaseTrades, bytes) ← decodeUInt 4 bytes
  let (purchaseVolume, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, dateOfTheTrade, price, bookValue, numberOfSalesTrades, salesVolume, numberOfPurchaseTrades, purchaseVolume }, bytes)

@[simp] theorem encode_length (message : MutualFundsTradesMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : MutualFundsTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MutualFundsTradesMessage) (rest : List UInt8) :
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

end MutualFundsTradesMessage

/-- Opening Of Continuous Auctions Message: 21 bytes -/
structure OpeningOfContinuousAuctionsMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  auctionSessionStartupTime : BitVec 64
  auctionSessionEndTime : BitVec 64
  deriving DecidableEq, Repr

namespace OpeningOfContinuousAuctionsMessage

def encode (message : OpeningOfContinuousAuctionsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.auctionSessionStartupTime
    ++ (encodeUInt 8 message.auctionSessionEndTime)))

def decode (bytes : List UInt8) : Option (OpeningOfContinuousAuctionsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (auctionSessionStartupTime, bytes) ← decodeUInt 8 bytes
  let (auctionSessionEndTime, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, auctionSessionStartupTime, auctionSessionEndTime }, bytes)

@[simp] theorem encode_length (message : OpeningOfContinuousAuctionsMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : OpeningOfContinuousAuctionsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OpeningOfContinuousAuctionsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OpeningOfContinuousAuctionsMessage

/-- Existence Of Bids At Mid Price Message: 6 bytes -/
structure ExistenceOfBidsAtMidPriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  bidsExisting : Alpha 1
  deriving DecidableEq, Repr

namespace ExistenceOfBidsAtMidPriceMessage

def encode (message : ExistenceOfBidsAtMidPriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.bidsExisting))

def decode (bytes : List UInt8) : Option (ExistenceOfBidsAtMidPriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (bidsExisting, bytes) ← Alpha.decode 1 bytes
  pure ({ instrumentNumber, origin, bidsExisting }, bytes)

@[simp] theorem encode_length (message : ExistenceOfBidsAtMidPriceMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ExistenceOfBidsAtMidPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExistenceOfBidsAtMidPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExistenceOfBidsAtMidPriceMessage

/-- Catalogue Of Debt And Metals Instruments Message: 103 bytes -/
structure CatalogueOfDebtAndMetalsInstrumentsMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  issuance : Alpha 6
  dateOfIssuance : BitVec 64
  dateOfMaturity : BitVec 64
  priceRateOfReference : BitVec 64
  dateOfReference : BitVec 64
  reference : Reference
  termDays : BitVec 16
  couponPeriod : BitVec 16
  isin : Alpha 12
  market : Market
  currentNominalValue : BitVec 64
  originalNominalValue : BitVec 64
  outstandingShares : BitVec 64
  amountPlaced : BitVec 64
  tradesRatePrice : TradesRatePrice
  deriving DecidableEq, Repr

namespace CatalogueOfDebtAndMetalsInstrumentsMessage

def encode (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.issuance
    ++ (encodeUInt 8 message.dateOfIssuance
    ++ (encodeUInt 8 message.dateOfMaturity
    ++ (encodeUInt 8 message.priceRateOfReference
    ++ (encodeUInt 8 message.dateOfReference
    ++ (Reference.encode message.reference
    ++ (encodeUInt 2 message.termDays
    ++ (encodeUInt 2 message.couponPeriod
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.currentNominalValue
    ++ (encodeUInt 8 message.originalNominalValue
    ++ (encodeUInt 8 message.outstandingShares
    ++ (encodeUInt 8 message.amountPlaced
    ++ (TradesRatePrice.encode message.tradesRatePrice))))))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogueOfDebtAndMetalsInstrumentsMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (issuance, bytes) ← Alpha.decode 6 bytes
  let (dateOfIssuance, bytes) ← decodeUInt 8 bytes
  let (dateOfMaturity, bytes) ← decodeUInt 8 bytes
  let (priceRateOfReference, bytes) ← decodeUInt 8 bytes
  let (dateOfReference, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (termDays, bytes) ← decodeUInt 2 bytes
  let (couponPeriod, bytes) ← decodeUInt 2 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (currentNominalValue, bytes) ← decodeUInt 8 bytes
  let (originalNominalValue, bytes) ← decodeUInt 8 bytes
  let (outstandingShares, bytes) ← decodeUInt 8 bytes
  let (amountPlaced, bytes) ← decodeUInt 8 bytes
  let (tradesRatePrice, bytes) ← TradesRatePrice.decode bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, issuance, dateOfIssuance, dateOfMaturity, priceRateOfReference, dateOfReference, reference, termDays, couponPeriod, isin, market, currentNominalValue, originalNominalValue, outstandingShares, amountPlaced, tradesRatePrice }, bytes)

@[simp] theorem encode_length (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : (encode message).length = 103 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, Reference.encode_length, Market.encode_length, TradesRatePrice.encode_length]

theorem encode_length_pos (message : CatalogueOfDebtAndMetalsInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogueOfDebtAndMetalsInstrumentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradesRatePrice.decode_encode, some_bind]
  rfl

end CatalogueOfDebtAndMetalsInstrumentsMessage

/-- Catalog Sent For Instruments Belonging To Mutual Funds Message: 78 bytes -/
structure CatalogSentForInstrumentsBelongingToMutualFundsMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  sector : BitVec 8
  subsector : BitVec 8
  industry : BitVec 8
  subIndustry : BitVec 8
  tradingCompany : Alpha 10
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  isin : Alpha 12
  rating : Alpha 15
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToMutualFundsMessage

def encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (encodeUInt 1 message.sector
    ++ (encodeUInt 1 message.subsector
    ++ (encodeUInt 1 message.industry
    ++ (encodeUInt 1 message.subIndustry
    ++ (Alpha.encode message.tradingCompany
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.rating))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToMutualFundsMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (sector, bytes) ← decodeUInt 1 bytes
  let (subsector, bytes) ← decodeUInt 1 bytes
  let (industry, bytes) ← decodeUInt 1 bytes
  let (subIndustry, bytes) ← decodeUInt 1 bytes
  let (tradingCompany, bytes) ← Alpha.decode 10 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (rating, bytes) ← Alpha.decode 15 bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, series, sector, subsector, industry, subIndustry, tradingCompany, referencePrice, referenceDate, reference, isin, rating }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, Reference.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToMutualFundsMessage

/-- Weighted Average Price Message: 21 bytes -/
structure WeightedAveragePriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  weightedAveragePrice : BitVec 64
  volatility : BitVec 64
  deriving DecidableEq, Repr

namespace WeightedAveragePriceMessage

def encode (message : WeightedAveragePriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.weightedAveragePrice
    ++ (encodeUInt 8 message.volatility)))

def decode (bytes : List UInt8) : Option (WeightedAveragePriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (weightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (volatility, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, weightedAveragePrice, volatility }, bytes)

@[simp] theorem encode_length (message : WeightedAveragePriceMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : WeightedAveragePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WeightedAveragePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WeightedAveragePriceMessage

/-- System Events Message: 31 bytes -/
structure SystemEventsMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  codeOfEvent : CodeOfEvent
  market : Market
  sendTime : BitVec 64
  endTime : BitVec 64
  group : Alpha 8
  deriving DecidableEq, Repr

namespace SystemEventsMessage

def encode (message : SystemEventsMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (CodeOfEvent.encode message.codeOfEvent
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.sendTime
    ++ (encodeUInt 8 message.endTime
    ++ (Alpha.encode message.group))))))

def decode (bytes : List UInt8) : Option (SystemEventsMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (codeOfEvent, bytes) ← CodeOfEvent.decode bytes
  let (market, bytes) ← Market.decode bytes
  let (sendTime, bytes) ← decodeUInt 8 bytes
  let (endTime, bytes) ← decodeUInt 8 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentNumber, origin, codeOfEvent, market, sendTime, endTime, group }, bytes)

@[simp] theorem encode_length (message : SystemEventsMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, CodeOfEvent.encode_length, Market.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CodeOfEvent.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventsMessage

/-- Reference Price Message: 14 bytes -/
structure ReferencePriceMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  price : BitVec 64
  priceType : PriceType
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.price
    ++ (PriceType.encode message.priceType)))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  pure ({ instrumentNumber, origin, price, priceType }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, PriceType.encode_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PriceType.decode_encode, some_bind]
  rfl

end ReferencePriceMessage

/-- Changes In Status Message: 7 bytes -/
structure ChangesInStatusMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  status : Status
  reason : Reason
  deriving DecidableEq, Repr

namespace ChangesInStatusMessage

def encode (message : ChangesInStatusMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (Status.encode message.status
    ++ (Reason.encode message.reason)))

def decode (bytes : List UInt8) : Option (ChangesInStatusMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (status, bytes) ← Status.decode bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ instrumentNumber, origin, status, reason }, bytes)

@[simp] theorem encode_length (message : ChangesInStatusMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Status.encode_length, Reason.encode_length]

theorem encode_length_pos (message : ChangesInStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChangesInStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Status.decode_encode, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end ChangesInStatusMessage

/-- Catalog For Instruments Belonging To The Capital Warrants Market Message: 66 bytes -/
structure CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage where
  numberOfTheInstrument : BitVec 32
  origin : Origin
  typeOfValue : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  typeOfWarrant : TypeOfWarrant
  dateOfMaturity : BitVec 64
  priceOfExercise : BitVec 64
  referencePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  isin : Alpha 12
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheInstrument
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.typeOfValue
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (TypeOfWarrant.encode message.typeOfWarrant
    ++ (encodeUInt 8 message.dateOfMaturity
    ++ (encodeUInt 8 message.priceOfExercise
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (Alpha.encode message.isin)))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage × List UInt8) := do
  let (numberOfTheInstrument, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (typeOfValue, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (typeOfWarrant, bytes) ← TypeOfWarrant.decode bytes
  let (dateOfMaturity, bytes) ← decodeUInt 8 bytes
  let (priceOfExercise, bytes) ← decodeUInt 8 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  pure ({ numberOfTheInstrument, origin, typeOfValue, issuingCompany, series, typeOfWarrant, dateOfMaturity, priceOfExercise, referencePrice, referenceDate, reference, isin }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length, TypeOfWarrant.encode_length, Reference.encode_length]

theorem encode_length_pos (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfWarrant.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage

/-- Catalog Sent For Instruments Belonging To Capital Tracs Message: 82 bytes -/
structure CatalogSentForInstrumentsBelongingToCapitalTracsMessage where
  numberOfTheTrac : BitVec 32
  origin : Origin
  nameOfTheTrac : Alpha 8
  underlyingIssuingCompany : Alpha 7
  underlyingSeries : Alpha 6
  securities : BitVec 64
  excludedSecurities : BitVec 64
  price : BitVec 64
  componentInCash : BitVec 64
  excludedValue : BitVec 64
  numberOfCertificates : BitVec 64
  theoreticalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CatalogSentForInstrumentsBelongingToCapitalTracsMessage

def encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheTrac
    ++ (Origin.encode message.origin
    ++ (Alpha.encode message.nameOfTheTrac
    ++ (Alpha.encode message.underlyingIssuingCompany
    ++ (Alpha.encode message.underlyingSeries
    ++ (encodeUInt 8 message.securities
    ++ (encodeUInt 8 message.excludedSecurities
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.componentInCash
    ++ (encodeUInt 8 message.excludedValue
    ++ (encodeUInt 8 message.numberOfCertificates
    ++ (encodeUInt 8 message.theoreticalPrice)))))))))))

def decode (bytes : List UInt8) : Option (CatalogSentForInstrumentsBelongingToCapitalTracsMessage × List UInt8) := do
  let (numberOfTheTrac, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (nameOfTheTrac, bytes) ← Alpha.decode 8 bytes
  let (underlyingIssuingCompany, bytes) ← Alpha.decode 7 bytes
  let (underlyingSeries, bytes) ← Alpha.decode 6 bytes
  let (securities, bytes) ← decodeUInt 8 bytes
  let (excludedSecurities, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (componentInCash, bytes) ← decodeUInt 8 bytes
  let (excludedValue, bytes) ← decodeUInt 8 bytes
  let (numberOfCertificates, bytes) ← decodeUInt 8 bytes
  let (theoreticalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ numberOfTheTrac, origin, nameOfTheTrac, underlyingIssuingCompany, underlyingSeries, securities, excludedSecurities, price, componentInCash, excludedValue, numberOfCertificates, theoreticalPrice }, bytes)

@[simp] theorem encode_length (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CatalogSentForInstrumentsBelongingToCapitalTracsMessage

/-- Consolidated Inav Message: 13 bytes -/
structure ConsolidatedInavMessage where
  numberOfTheTrac : BitVec 32
  origin : Origin
  currentTheoreticalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace ConsolidatedInavMessage

def encode (message : ConsolidatedInavMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheTrac
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.currentTheoreticalPrice))

def decode (bytes : List UInt8) : Option (ConsolidatedInavMessage × List UInt8) := do
  let (numberOfTheTrac, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (currentTheoreticalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ numberOfTheTrac, origin, currentTheoreticalPrice }, bytes)

@[simp] theorem encode_length (message : ConsolidatedInavMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ConsolidatedInavMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedInavMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedInavMessage

/-- Catalog For Instruments Belonging To The Local And Global Stock Market Message: 73 bytes -/
structure CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage where
  mseInstrumentNumber : BitVec 32
  valueOfType : Alpha 2
  issuingCompany : Alpha 7
  series : Alpha 6
  lastPrice : BitVec 64
  pppWeightedAveragePrice : BitVec 64
  referenceDate : BitVec 64
  reference : Reference
  couponInEffect : BitVec 16
  marketability : Marketability
  numericalMarketability : BitVec 32
  isin : Alpha 12
  market : Market
  registeredValues : BitVec 64
  exchange : Exchange
  deriving DecidableEq, Repr

namespace CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

def encode (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : List UInt8 :=
  encodeUInt 4 message.mseInstrumentNumber
    ++ (Alpha.encode message.valueOfType
    ++ (Alpha.encode message.issuingCompany
    ++ (Alpha.encode message.series
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 8 message.pppWeightedAveragePrice
    ++ (encodeUInt 8 message.referenceDate
    ++ (Reference.encode message.reference
    ++ (encodeUInt 2 message.couponInEffect
    ++ (Marketability.encode message.marketability
    ++ (encodeUInt 4 message.numericalMarketability
    ++ (Alpha.encode message.isin
    ++ (Market.encode message.market
    ++ (encodeUInt 8 message.registeredValues
    ++ (Exchange.encode message.exchange))))))))))))))

def decode (bytes : List UInt8) : Option (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage × List UInt8) := do
  let (mseInstrumentNumber, bytes) ← decodeUInt 4 bytes
  let (valueOfType, bytes) ← Alpha.decode 2 bytes
  let (issuingCompany, bytes) ← Alpha.decode 7 bytes
  let (series, bytes) ← Alpha.decode 6 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (pppWeightedAveragePrice, bytes) ← decodeUInt 8 bytes
  let (referenceDate, bytes) ← decodeUInt 8 bytes
  let (reference, bytes) ← Reference.decode bytes
  let (couponInEffect, bytes) ← decodeUInt 2 bytes
  let (marketability, bytes) ← Marketability.decode bytes
  let (numericalMarketability, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (market, bytes) ← Market.decode bytes
  let (registeredValues, bytes) ← decodeUInt 8 bytes
  let (exchange, bytes) ← Exchange.decode bytes
  pure ({ mseInstrumentNumber, valueOfType, issuingCompany, series, lastPrice, pppWeightedAveragePrice, referenceDate, reference, couponInEffect, marketability, numericalMarketability, isin, market, registeredValues, exchange }, bytes)

@[simp] theorem encode_length (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Reference.encode_length, Marketability.encode_length, Market.encode_length, Exchange.encode_length]

theorem encode_length_pos (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Reference.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Marketability.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Market.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Exchange.decode_encode, some_bind]
  rfl

end CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage

/-- Probable Price Of Allocation Message: 21 bytes -/
structure ProbablePriceOfAllocationMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  probablePriceOfAllocation : BitVec 64
  volumeInt648 : BitVec 64
  deriving DecidableEq, Repr

namespace ProbablePriceOfAllocationMessage

def encode (message : ProbablePriceOfAllocationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.probablePriceOfAllocation
    ++ (encodeUInt 8 message.volumeInt648)))

def decode (bytes : List UInt8) : Option (ProbablePriceOfAllocationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (probablePriceOfAllocation, bytes) ← decodeUInt 8 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, probablePriceOfAllocation, volumeInt648 }, bytes)

@[simp] theorem encode_length (message : ProbablePriceOfAllocationMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ProbablePriceOfAllocationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProbablePriceOfAllocationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ProbablePriceOfAllocationMessage

/-- Relation Between Bmvbiva Instruments Message: 9 bytes -/
structure RelationBetweenBmvbivaInstrumentsMessage where
  numberOfTheBmvInstrument : BitVec 32
  bivaInstrument : BitVec 32
  typeOfTrading : TypeOfTrading
  deriving DecidableEq, Repr

namespace RelationBetweenBmvbivaInstrumentsMessage

def encode (message : RelationBetweenBmvbivaInstrumentsMessage) : List UInt8 :=
  encodeUInt 4 message.numberOfTheBmvInstrument
    ++ (encodeUInt 4 message.bivaInstrument
    ++ (TypeOfTrading.encode message.typeOfTrading))

def decode (bytes : List UInt8) : Option (RelationBetweenBmvbivaInstrumentsMessage × List UInt8) := do
  let (numberOfTheBmvInstrument, bytes) ← decodeUInt 4 bytes
  let (bivaInstrument, bytes) ← decodeUInt 4 bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  pure ({ numberOfTheBmvInstrument, bivaInstrument, typeOfTrading }, bytes)

@[simp] theorem encode_length (message : RelationBetweenBmvbivaInstrumentsMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TypeOfTrading.encode_length]

theorem encode_length_pos (message : RelationBetweenBmvbivaInstrumentsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelationBetweenBmvbivaInstrumentsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TypeOfTrading.decode_encode, some_bind]
  rfl

end RelationBetweenBmvbivaInstrumentsMessage

/-- Equities Market Trades Message: 61 bytes -/
structure EquitiesMarketTradesMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  timeOfTheTrade : BitVec 64
  volumeInt648 : BitVec 64
  price : BitVec 64
  typeOfAgreement : TypeOfAgreement
  consecutiveNumberOfTheTrade : BitVec 64
  setsPrice : Alpha 1
  typeOfTrading : TypeOfTrading
  amount : BitVec 64
  purchases : Alpha 5
  sells : Alpha 5
  settlement : Settlement
  auctionIndicator : AuctionIndicator
  indicator : Indicator
  deriving DecidableEq, Repr

namespace EquitiesMarketTradesMessage

def encode (message : EquitiesMarketTradesMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.timeOfTheTrade
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.price
    ++ (TypeOfAgreement.encode message.typeOfAgreement
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade
    ++ (Alpha.encode message.setsPrice
    ++ (TypeOfTrading.encode message.typeOfTrading
    ++ (encodeUInt 8 message.amount
    ++ (Alpha.encode message.purchases
    ++ (Alpha.encode message.sells
    ++ (Settlement.encode message.settlement
    ++ (AuctionIndicator.encode message.auctionIndicator
    ++ (Indicator.encode message.indicator))))))))))))))

def decode (bytes : List UInt8) : Option (EquitiesMarketTradesMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (timeOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (typeOfAgreement, bytes) ← TypeOfAgreement.decode bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (setsPrice, bytes) ← Alpha.decode 1 bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  let (amount, bytes) ← decodeUInt 8 bytes
  let (purchases, bytes) ← Alpha.decode 5 bytes
  let (sells, bytes) ← Alpha.decode 5 bytes
  let (settlement, bytes) ← Settlement.decode bytes
  let (auctionIndicator, bytes) ← AuctionIndicator.decode bytes
  let (indicator, bytes) ← Indicator.decode bytes
  pure ({ instrumentNumber, origin, timeOfTheTrade, volumeInt648, price, typeOfAgreement, consecutiveNumberOfTheTrade, setsPrice, typeOfTrading, amount, purchases, sells, settlement, auctionIndicator, indicator }, bytes)

@[simp] theorem encode_length (message : EquitiesMarketTradesMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, TypeOfAgreement.encode_length, Alpha.encode_length, TypeOfTrading.encode_length, Settlement.encode_length, AuctionIndicator.encode_length, Indicator.encode_length]

theorem encode_length_pos (message : EquitiesMarketTradesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquitiesMarketTradesMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfAgreement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TypeOfTrading.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Settlement.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionIndicator.decode_encode, some_bind]
  dsimp only
  rw [Indicator.decode_encode, some_bind]
  rfl

end EquitiesMarketTradesMessage

/-- Consolidated Trade Cancellation Message: 13 bytes -/
structure ConsolidatedTradeCancellationMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  consecutiveNumberOfTheTrade : BitVec 64
  deriving DecidableEq, Repr

namespace ConsolidatedTradeCancellationMessage

def encode (message : ConsolidatedTradeCancellationMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade))

def decode (bytes : List UInt8) : Option (ConsolidatedTradeCancellationMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, consecutiveNumberOfTheTrade }, bytes)

@[simp] theorem encode_length (message : ConsolidatedTradeCancellationMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : ConsolidatedTradeCancellationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedTradeCancellationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConsolidatedTradeCancellationMessage

/-- Pricevolume Indicator Message: 38 bytes -/
structure PricevolumeIndicatorMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  probablePriceOfAllotment : BitVec 64
  volumeInt648 : BitVec 64
  bestSellingPrice : BitVec 64
  bestPurchasingPrice : BitVec 64
  typeOfCrossTrading : TypeOfCrossTrading
  deriving DecidableEq, Repr

namespace PricevolumeIndicatorMessage

def encode (message : PricevolumeIndicatorMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.probablePriceOfAllotment
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.bestSellingPrice
    ++ (encodeUInt 8 message.bestPurchasingPrice
    ++ (TypeOfCrossTrading.encode message.typeOfCrossTrading))))))

def decode (bytes : List UInt8) : Option (PricevolumeIndicatorMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (probablePriceOfAllotment, bytes) ← decodeUInt 8 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (bestSellingPrice, bytes) ← decodeUInt 8 bytes
  let (bestPurchasingPrice, bytes) ← decodeUInt 8 bytes
  let (typeOfCrossTrading, bytes) ← TypeOfCrossTrading.decode bytes
  pure ({ instrumentNumber, origin, probablePriceOfAllotment, volumeInt648, bestSellingPrice, bestPurchasingPrice, typeOfCrossTrading }, bytes)

@[simp] theorem encode_length (message : PricevolumeIndicatorMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, TypeOfCrossTrading.encode_length]

theorem encode_length_pos (message : PricevolumeIndicatorMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PricevolumeIndicatorMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TypeOfCrossTrading.decode_encode, some_bind]
  rfl

end PricevolumeIndicatorMessage

/-- Consolidated Execution Of Orders Message: 52 bytes -/
structure ConsolidatedExecutionOfOrdersMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  date : BitVec 64
  consecutiveNumber : BitVec 64
  volumeInt648 : BitVec 64
  consecutiveNumberOfTheTrade : BitVec 64
  executionPrice : BitVec 64
  indicator : Indicator
  setsPrice : Alpha 1
  participant : Alpha 5
  deriving DecidableEq, Repr

namespace ConsolidatedExecutionOfOrdersMessage

def encode (message : ConsolidatedExecutionOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.consecutiveNumber
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.consecutiveNumberOfTheTrade
    ++ (encodeUInt 8 message.executionPrice
    ++ (Indicator.encode message.indicator
    ++ (Alpha.encode message.setsPrice
    ++ (Alpha.encode message.participant)))))))))

def decode (bytes : List UInt8) : Option (ConsolidatedExecutionOfOrdersMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumberOfTheTrade, bytes) ← decodeUInt 8 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (indicator, bytes) ← Indicator.decode bytes
  let (setsPrice, bytes) ← Alpha.decode 1 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, origin, date, consecutiveNumber, volumeInt648, consecutiveNumberOfTheTrade, executionPrice, indicator, setsPrice, participant }, bytes)

@[simp] theorem encode_length (message : ConsolidatedExecutionOfOrdersMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Indicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ConsolidatedExecutionOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConsolidatedExecutionOfOrdersMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Indicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConsolidatedExecutionOfOrdersMessage

/-- Registration Of Order Message: 43 bytes -/
structure RegistrationOfOrderMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  dateAndTime : BitVec 64
  consecutiveNumber : BitVec 64
  direction : Direction
  volumeInt648 : BitVec 64
  price : BitVec 64
  participant : Alpha 5
  deriving DecidableEq, Repr

namespace RegistrationOfOrderMessage

def encode (message : RegistrationOfOrderMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.dateAndTime
    ++ (encodeUInt 8 message.consecutiveNumber
    ++ (Direction.encode message.direction
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.price
    ++ (Alpha.encode message.participant)))))))

def decode (bytes : List UInt8) : Option (RegistrationOfOrderMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (dateAndTime, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  let (direction, bytes) ← Direction.decode bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (participant, bytes) ← Alpha.decode 5 bytes
  pure ({ instrumentNumber, origin, dateAndTime, consecutiveNumber, direction, volumeInt648, price, participant }, bytes)

@[simp] theorem encode_length (message : RegistrationOfOrderMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length, Direction.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RegistrationOfOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegistrationOfOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Direction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RegistrationOfOrderMessage

/-- Cancellations Of Orders Message: 21 bytes -/
structure CancellationsOfOrdersMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  date : BitVec 64
  consecutiveNumber : BitVec 64
  deriving DecidableEq, Repr

namespace CancellationsOfOrdersMessage

def encode (message : CancellationsOfOrdersMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.date
    ++ (encodeUInt 8 message.consecutiveNumber)))

def decode (bytes : List UInt8) : Option (CancellationsOfOrdersMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (date, bytes) ← decodeUInt 8 bytes
  let (consecutiveNumber, bytes) ← decodeUInt 8 bytes
  pure ({ instrumentNumber, origin, date, consecutiveNumber }, bytes)

@[simp] theorem encode_length (message : CancellationsOfOrdersMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Origin.encode_length]

theorem encode_length_pos (message : CancellationsOfOrdersMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancellationsOfOrdersMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Origin.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancellationsOfOrdersMessage

/-- Last Quote Message: 23 bytes -/
structure LastQuoteMessage where
  instrumentNumber : BitVec 32
  origin : Origin
  volumeInt648 : BitVec 64
  priceRate : BitVec 64
  directionOfTheBid : DirectionOfTheBid
  typeOfTrading : TypeOfTrading
  deriving DecidableEq, Repr

namespace LastQuoteMessage

def encode (message : LastQuoteMessage) : List UInt8 :=
  encodeUInt 4 message.instrumentNumber
    ++ (Origin.encode message.origin
    ++ (encodeUInt 8 message.volumeInt648
    ++ (encodeUInt 8 message.priceRate
    ++ (DirectionOfTheBid.encode message.directionOfTheBid
    ++ (TypeOfTrading.encode message.typeOfTrading)))))

def decode (bytes : List UInt8) : Option (LastQuoteMessage × List UInt8) := do
  let (instrumentNumber, bytes) ← decodeUInt 4 bytes
  let (origin, bytes) ← Origin.decode bytes
  let (volumeInt648, bytes) ← decodeUInt 8 bytes
  let (priceRate, bytes) ← decodeUInt 8 bytes
  let (directionOfTheBid, bytes) ← DirectionOfTheBid.decode bytes
  let (typeOfTrading, bytes) ← TypeOfTrading.decode bytes
  pure ({ instrumentNumber, origin, volumeInt648, priceRate, directionOfTheBid, typeOfTrading }, bytes)

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

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginResponseMessage (message : LoginResponseMessage) -- 38
  | replayResponseMessage (message : ReplayResponseMessage) -- 42
  | snapshotResponseMessage (message : SnapshotResponseMessage) -- 43
  | snapshotCompleteMessage (message : SnapshotCompleteMessage) -- 63
  | eventsSystemMessage (message : EventsSystemMessage) -- 83
  | tradeCancellationMessage (message : TradeCancellationMessage) -- 72
  | statusChangesMessage (message : StatusChangesMessage) -- 52
  | weightedAveragePriceSettlementPricesMessage (message : WeightedAveragePriceSettlementPricesMessage) -- 77
  | capitalTradesMessage (message : CapitalTradesMessage) -- 80
  | probableAllocationPriceMessage (message : ProbableAllocationPriceMessage) -- 50
  | continuousAuctionsBeginningMessage (message : ContinuousAuctionsBeginningMessage) -- 51
  | middlePriceExistingQuotesMessage (message : MiddlePriceExistingQuotesMessage) -- 53
  | registryOperationsMessage (message : RegistryOperationsMessage) -- 90
  | mutualFundTradesMessage (message : MutualFundTradesMessage) -- 89
  | tradabilityMessage (message : TradabilityMessage) -- 69
  | virtualTradesMessage (message : VirtualTradesMessage) -- 86
  | orderAdditionMessage (message : OrderAdditionMessage) -- 65
  | executionOfOrdersMessage (message : ExecutionOfOrdersMessage) -- 67
  | orderCancellationMessage (message : OrderCancellationMessage) -- 68
  | orderChangeMessage (message : OrderChangeMessage) -- 70
  | depthMessage (message : DepthMessage) -- 49
  | bestOfferMessage (message : BestOfferMessage) -- 79
  | publicOfferingsMessage (message : PublicOfferingsMessage) -- 66
  | openInterestMessage (message : OpenInterestMessage) -- 73
  | derivativesMarketTradesMessage (message : DerivativesMarketTradesMessage) -- 81
  | statisticsOfInstrumentsMessage (message : StatisticsOfInstrumentsMessage) -- 82
  | generalIndicesMessage (message : GeneralIndicesMessage) -- 85
  | indicesComponentsMessage (message : IndicesComponentsMessage) -- 87
  | inavMessage (message : InavMessage) -- 71
  | dollarBuySellMessage (message : DollarBuySellMessage) -- 114
  | shortSalesBalancesPerInstrumentMessage (message : ShortSalesBalancesPerInstrumentMessage) -- 115
  | capitalMarketMultiplesMessage (message : CapitalMarketMultiplesMessage) -- 116
  | benchmarkMessage (message : BenchmarkMessage) -- 120
  | capitalizationRulesMessage (message : CapitalizationRulesMessage) -- 122
  | closingPriceOriginMessage (message : ClosingPriceOriginMessage) -- 126
  | mutualFundsTradesMessage (message : MutualFundsTradesMessage) -- 40
  | openingOfContinuousAuctionsMessage (message : OpeningOfContinuousAuctionsMessage) -- 41
  | existenceOfBidsAtMidPriceMessage (message : ExistenceOfBidsAtMidPriceMessage) -- 44
  | catalogueOfDebtAndMetalsInstrumentsMessage (message : CatalogueOfDebtAndMetalsInstrumentsMessage) -- 46
  | catalogSentForInstrumentsBelongingToMutualFundsMessage (message : CatalogSentForInstrumentsBelongingToMutualFundsMessage) -- 48
  | weightedAveragePriceMessage (message : WeightedAveragePriceMessage) -- 54
  | systemEventsMessage (message : SystemEventsMessage) -- 55
  | referencePriceMessage (message : ReferencePriceMessage) -- 56
  | changesInStatusMessage (message : ChangesInStatusMessage) -- 57
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage (message : CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage) -- 84
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage (message : CatalogSentForInstrumentsBelongingToCapitalTracsMessage) -- 91
  | consolidatedInavMessage (message : ConsolidatedInavMessage) -- 93
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage (message : CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage) -- 104
  | probablePriceOfAllocationMessage (message : ProbablePriceOfAllocationMessage) -- 105
  | relationBetweenBmvbivaInstrumentsMessage (message : RelationBetweenBmvbivaInstrumentsMessage) -- 106
  | equitiesMarketTradesMessage (message : EquitiesMarketTradesMessage) -- 112
  | consolidatedTradeCancellationMessage (message : ConsolidatedTradeCancellationMessage) -- 113
  | pricevolumeIndicatorMessage (message : PricevolumeIndicatorMessage) -- 92
  | consolidatedExecutionOfOrdersMessage (message : ConsolidatedExecutionOfOrdersMessage) -- 107
  | registrationOfOrderMessage (message : RegistrationOfOrderMessage) -- 110
  | cancellationsOfOrdersMessage (message : CancellationsOfOrdersMessage) -- 117
  | lastQuoteMessage (message : LastQuoteMessage) -- 109
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginResponseMessage _ => 38
  | .replayResponseMessage _ => 42
  | .snapshotResponseMessage _ => 43
  | .snapshotCompleteMessage _ => 63
  | .eventsSystemMessage _ => 83
  | .tradeCancellationMessage _ => 72
  | .statusChangesMessage _ => 52
  | .weightedAveragePriceSettlementPricesMessage _ => 77
  | .capitalTradesMessage _ => 80
  | .probableAllocationPriceMessage _ => 50
  | .continuousAuctionsBeginningMessage _ => 51
  | .middlePriceExistingQuotesMessage _ => 53
  | .registryOperationsMessage _ => 90
  | .mutualFundTradesMessage _ => 89
  | .tradabilityMessage _ => 69
  | .virtualTradesMessage _ => 86
  | .orderAdditionMessage _ => 65
  | .executionOfOrdersMessage _ => 67
  | .orderCancellationMessage _ => 68
  | .orderChangeMessage _ => 70
  | .depthMessage _ => 49
  | .bestOfferMessage _ => 79
  | .publicOfferingsMessage _ => 66
  | .openInterestMessage _ => 73
  | .derivativesMarketTradesMessage _ => 81
  | .statisticsOfInstrumentsMessage _ => 82
  | .generalIndicesMessage _ => 85
  | .indicesComponentsMessage _ => 87
  | .inavMessage _ => 71
  | .dollarBuySellMessage _ => 114
  | .shortSalesBalancesPerInstrumentMessage _ => 115
  | .capitalMarketMultiplesMessage _ => 116
  | .benchmarkMessage _ => 120
  | .capitalizationRulesMessage _ => 122
  | .closingPriceOriginMessage _ => 126
  | .mutualFundsTradesMessage _ => 40
  | .openingOfContinuousAuctionsMessage _ => 41
  | .existenceOfBidsAtMidPriceMessage _ => 44
  | .catalogueOfDebtAndMetalsInstrumentsMessage _ => 46
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage _ => 48
  | .weightedAveragePriceMessage _ => 54
  | .systemEventsMessage _ => 55
  | .referencePriceMessage _ => 56
  | .changesInStatusMessage _ => 57
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage _ => 84
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage _ => 91
  | .consolidatedInavMessage _ => 93
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage _ => 104
  | .probablePriceOfAllocationMessage _ => 105
  | .relationBetweenBmvbivaInstrumentsMessage _ => 106
  | .equitiesMarketTradesMessage _ => 112
  | .consolidatedTradeCancellationMessage _ => 113
  | .pricevolumeIndicatorMessage _ => 92
  | .consolidatedExecutionOfOrdersMessage _ => 107
  | .registrationOfOrderMessage _ => 110
  | .cancellationsOfOrdersMessage _ => 117
  | .lastQuoteMessage _ => 109

def encode : Payload → List UInt8
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .replayResponseMessage message => ReplayResponseMessage.encode message
  | .snapshotResponseMessage message => SnapshotResponseMessage.encode message
  | .snapshotCompleteMessage message => SnapshotCompleteMessage.encode message
  | .eventsSystemMessage message => EventsSystemMessage.encode message
  | .tradeCancellationMessage message => TradeCancellationMessage.encode message
  | .statusChangesMessage message => StatusChangesMessage.encode message
  | .weightedAveragePriceSettlementPricesMessage message => WeightedAveragePriceSettlementPricesMessage.encode message
  | .capitalTradesMessage message => CapitalTradesMessage.encode message
  | .probableAllocationPriceMessage message => ProbableAllocationPriceMessage.encode message
  | .continuousAuctionsBeginningMessage message => ContinuousAuctionsBeginningMessage.encode message
  | .middlePriceExistingQuotesMessage message => MiddlePriceExistingQuotesMessage.encode message
  | .registryOperationsMessage message => RegistryOperationsMessage.encode message
  | .mutualFundTradesMessage message => MutualFundTradesMessage.encode message
  | .tradabilityMessage message => TradabilityMessage.encode message
  | .virtualTradesMessage message => VirtualTradesMessage.encode message
  | .orderAdditionMessage message => OrderAdditionMessage.encode message
  | .executionOfOrdersMessage message => ExecutionOfOrdersMessage.encode message
  | .orderCancellationMessage message => OrderCancellationMessage.encode message
  | .orderChangeMessage message => OrderChangeMessage.encode message
  | .depthMessage message => DepthMessage.encode message
  | .bestOfferMessage message => BestOfferMessage.encode message
  | .publicOfferingsMessage message => PublicOfferingsMessage.encode message
  | .openInterestMessage message => OpenInterestMessage.encode message
  | .derivativesMarketTradesMessage message => DerivativesMarketTradesMessage.encode message
  | .statisticsOfInstrumentsMessage message => StatisticsOfInstrumentsMessage.encode message
  | .generalIndicesMessage message => GeneralIndicesMessage.encode message
  | .indicesComponentsMessage message => IndicesComponentsMessage.encode message
  | .inavMessage message => InavMessage.encode message
  | .dollarBuySellMessage message => DollarBuySellMessage.encode message
  | .shortSalesBalancesPerInstrumentMessage message => ShortSalesBalancesPerInstrumentMessage.encode message
  | .capitalMarketMultiplesMessage message => CapitalMarketMultiplesMessage.encode message
  | .benchmarkMessage message => BenchmarkMessage.encode message
  | .capitalizationRulesMessage message => CapitalizationRulesMessage.encode message
  | .closingPriceOriginMessage message => ClosingPriceOriginMessage.encode message
  | .mutualFundsTradesMessage message => MutualFundsTradesMessage.encode message
  | .openingOfContinuousAuctionsMessage message => OpeningOfContinuousAuctionsMessage.encode message
  | .existenceOfBidsAtMidPriceMessage message => ExistenceOfBidsAtMidPriceMessage.encode message
  | .catalogueOfDebtAndMetalsInstrumentsMessage message => CatalogueOfDebtAndMetalsInstrumentsMessage.encode message
  | .catalogSentForInstrumentsBelongingToMutualFundsMessage message => CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode message
  | .weightedAveragePriceMessage message => WeightedAveragePriceMessage.encode message
  | .systemEventsMessage message => SystemEventsMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .changesInStatusMessage message => ChangesInStatusMessage.encode message
  | .catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message => CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode message
  | .catalogSentForInstrumentsBelongingToCapitalTracsMessage message => CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode message
  | .consolidatedInavMessage message => ConsolidatedInavMessage.encode message
  | .catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message => CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode message
  | .probablePriceOfAllocationMessage message => ProbablePriceOfAllocationMessage.encode message
  | .relationBetweenBmvbivaInstrumentsMessage message => RelationBetweenBmvbivaInstrumentsMessage.encode message
  | .equitiesMarketTradesMessage message => EquitiesMarketTradesMessage.encode message
  | .consolidatedTradeCancellationMessage message => ConsolidatedTradeCancellationMessage.encode message
  | .pricevolumeIndicatorMessage message => PricevolumeIndicatorMessage.encode message
  | .consolidatedExecutionOfOrdersMessage message => ConsolidatedExecutionOfOrdersMessage.encode message
  | .registrationOfOrderMessage message => RegistrationOfOrderMessage.encode message
  | .cancellationsOfOrdersMessage message => CancellationsOfOrdersMessage.encode message
  | .lastQuoteMessage message => LastQuoteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 3576 := by
  cases message with
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [encode, ReplayResponseMessage.encode_length]
    omega
  | snapshotResponseMessage inner =>
    simp only [encode, SnapshotResponseMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [encode, SnapshotCompleteMessage.encode_length]
    omega
  | eventsSystemMessage inner =>
    simp only [encode, EventsSystemMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [encode, TradeCancellationMessage.encode_length]
    omega
  | statusChangesMessage inner =>
    simp only [encode, StatusChangesMessage.encode_length]
    omega
  | weightedAveragePriceSettlementPricesMessage inner =>
    simp only [encode, WeightedAveragePriceSettlementPricesMessage.encode_length]
    omega
  | capitalTradesMessage inner =>
    simp only [encode, CapitalTradesMessage.encode_length]
    omega
  | probableAllocationPriceMessage inner =>
    simp only [encode, ProbableAllocationPriceMessage.encode_length]
    omega
  | continuousAuctionsBeginningMessage inner =>
    simp only [encode, ContinuousAuctionsBeginningMessage.encode_length]
    omega
  | middlePriceExistingQuotesMessage inner =>
    simp only [encode, MiddlePriceExistingQuotesMessage.encode_length]
    omega
  | registryOperationsMessage inner =>
    simp only [encode, RegistryOperationsMessage.encode_length]
    omega
  | mutualFundTradesMessage inner =>
    simp only [encode, MutualFundTradesMessage.encode_length]
    omega
  | tradabilityMessage inner =>
    simp only [encode, TradabilityMessage.encode_length]
    omega
  | virtualTradesMessage inner =>
    simp only [encode, VirtualTradesMessage.encode_length]
    omega
  | orderAdditionMessage inner =>
    simp only [encode, OrderAdditionMessage.encode_length]
    omega
  | executionOfOrdersMessage inner =>
    simp only [encode, ExecutionOfOrdersMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [encode, OrderCancellationMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [encode, OrderChangeMessage.encode_length]
    omega
  | depthMessage inner =>
    have bound_inner := DepthMessage.encode_length_le inner
    simp only [encode]
    omega
  | bestOfferMessage inner =>
    simp only [encode, BestOfferMessage.encode_length]
    omega
  | publicOfferingsMessage inner =>
    simp only [encode, PublicOfferingsMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [encode, OpenInterestMessage.encode_length]
    omega
  | derivativesMarketTradesMessage inner =>
    simp only [encode, DerivativesMarketTradesMessage.encode_length]
    omega
  | statisticsOfInstrumentsMessage inner =>
    simp only [encode, StatisticsOfInstrumentsMessage.encode_length]
    omega
  | generalIndicesMessage inner =>
    simp only [encode, GeneralIndicesMessage.encode_length]
    omega
  | indicesComponentsMessage inner =>
    simp only [encode, IndicesComponentsMessage.encode_length]
    omega
  | inavMessage inner =>
    simp only [encode, InavMessage.encode_length]
    omega
  | dollarBuySellMessage inner =>
    simp only [encode, DollarBuySellMessage.encode_length]
    omega
  | shortSalesBalancesPerInstrumentMessage inner =>
    simp only [encode, ShortSalesBalancesPerInstrumentMessage.encode_length]
    omega
  | capitalMarketMultiplesMessage inner =>
    simp only [encode, CapitalMarketMultiplesMessage.encode_length]
    omega
  | benchmarkMessage inner =>
    simp only [encode, BenchmarkMessage.encode_length]
    omega
  | capitalizationRulesMessage inner =>
    simp only [encode, CapitalizationRulesMessage.encode_length]
    omega
  | closingPriceOriginMessage inner =>
    simp only [encode, ClosingPriceOriginMessage.encode_length]
    omega
  | mutualFundsTradesMessage inner =>
    simp only [encode, MutualFundsTradesMessage.encode_length]
    omega
  | openingOfContinuousAuctionsMessage inner =>
    simp only [encode, OpeningOfContinuousAuctionsMessage.encode_length]
    omega
  | existenceOfBidsAtMidPriceMessage inner =>
    simp only [encode, ExistenceOfBidsAtMidPriceMessage.encode_length]
    omega
  | catalogueOfDebtAndMetalsInstrumentsMessage inner =>
    simp only [encode, CatalogueOfDebtAndMetalsInstrumentsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | weightedAveragePriceMessage inner =>
    simp only [encode, WeightedAveragePriceMessage.encode_length]
    omega
  | systemEventsMessage inner =>
    simp only [encode, SystemEventsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | changesInStatusMessage inner =>
    simp only [encode, ChangesInStatusMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [encode, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | consolidatedInavMessage inner =>
    simp only [encode, ConsolidatedInavMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [encode, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | probablePriceOfAllocationMessage inner =>
    simp only [encode, ProbablePriceOfAllocationMessage.encode_length]
    omega
  | relationBetweenBmvbivaInstrumentsMessage inner =>
    simp only [encode, RelationBetweenBmvbivaInstrumentsMessage.encode_length]
    omega
  | equitiesMarketTradesMessage inner =>
    simp only [encode, EquitiesMarketTradesMessage.encode_length]
    omega
  | consolidatedTradeCancellationMessage inner =>
    simp only [encode, ConsolidatedTradeCancellationMessage.encode_length]
    omega
  | pricevolumeIndicatorMessage inner =>
    simp only [encode, PricevolumeIndicatorMessage.encode_length]
    omega
  | consolidatedExecutionOfOrdersMessage inner =>
    simp only [encode, ConsolidatedExecutionOfOrdersMessage.encode_length]
    omega
  | registrationOfOrderMessage inner =>
    simp only [encode, RegistrationOfOrderMessage.encode_length]
    omega
  | cancellationsOfOrdersMessage inner =>
    simp only [encode, CancellationsOfOrdersMessage.encode_length]
    omega
  | lastQuoteMessage inner =>
    simp only [encode, LastQuoteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 38 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 42 then (ReplayResponseMessage.decode bytes).map fun (message, rest) => (.replayResponseMessage message, rest)
  else if tag = 43 then (SnapshotResponseMessage.decode bytes).map fun (message, rest) => (.snapshotResponseMessage message, rest)
  else if tag = 63 then (SnapshotCompleteMessage.decode bytes).map fun (message, rest) => (.snapshotCompleteMessage message, rest)
  else if tag = 83 then (EventsSystemMessage.decode bytes).map fun (message, rest) => (.eventsSystemMessage message, rest)
  else if tag = 72 then (TradeCancellationMessage.decode bytes).map fun (message, rest) => (.tradeCancellationMessage message, rest)
  else if tag = 52 then (StatusChangesMessage.decode bytes).map fun (message, rest) => (.statusChangesMessage message, rest)
  else if tag = 77 then (WeightedAveragePriceSettlementPricesMessage.decode bytes).map fun (message, rest) => (.weightedAveragePriceSettlementPricesMessage message, rest)
  else if tag = 80 then (CapitalTradesMessage.decode bytes).map fun (message, rest) => (.capitalTradesMessage message, rest)
  else if tag = 50 then (ProbableAllocationPriceMessage.decode bytes).map fun (message, rest) => (.probableAllocationPriceMessage message, rest)
  else if tag = 51 then (ContinuousAuctionsBeginningMessage.decode bytes).map fun (message, rest) => (.continuousAuctionsBeginningMessage message, rest)
  else if tag = 53 then (MiddlePriceExistingQuotesMessage.decode bytes).map fun (message, rest) => (.middlePriceExistingQuotesMessage message, rest)
  else if tag = 90 then (RegistryOperationsMessage.decode bytes).map fun (message, rest) => (.registryOperationsMessage message, rest)
  else if tag = 89 then (MutualFundTradesMessage.decode bytes).map fun (message, rest) => (.mutualFundTradesMessage message, rest)
  else if tag = 69 then (TradabilityMessage.decode bytes).map fun (message, rest) => (.tradabilityMessage message, rest)
  else if tag = 86 then (VirtualTradesMessage.decode bytes).map fun (message, rest) => (.virtualTradesMessage message, rest)
  else if tag = 65 then (OrderAdditionMessage.decode bytes).map fun (message, rest) => (.orderAdditionMessage message, rest)
  else if tag = 67 then (ExecutionOfOrdersMessage.decode bytes).map fun (message, rest) => (.executionOfOrdersMessage message, rest)
  else if tag = 68 then (OrderCancellationMessage.decode bytes).map fun (message, rest) => (.orderCancellationMessage message, rest)
  else if tag = 70 then (OrderChangeMessage.decode bytes).map fun (message, rest) => (.orderChangeMessage message, rest)
  else if tag = 49 then (DepthMessage.decode bytes).map fun (message, rest) => (.depthMessage message, rest)
  else if tag = 79 then (BestOfferMessage.decode bytes).map fun (message, rest) => (.bestOfferMessage message, rest)
  else if tag = 66 then (PublicOfferingsMessage.decode bytes).map fun (message, rest) => (.publicOfferingsMessage message, rest)
  else if tag = 73 then (OpenInterestMessage.decode bytes).map fun (message, rest) => (.openInterestMessage message, rest)
  else if tag = 81 then (DerivativesMarketTradesMessage.decode bytes).map fun (message, rest) => (.derivativesMarketTradesMessage message, rest)
  else if tag = 82 then (StatisticsOfInstrumentsMessage.decode bytes).map fun (message, rest) => (.statisticsOfInstrumentsMessage message, rest)
  else if tag = 85 then (GeneralIndicesMessage.decode bytes).map fun (message, rest) => (.generalIndicesMessage message, rest)
  else if tag = 87 then (IndicesComponentsMessage.decode bytes).map fun (message, rest) => (.indicesComponentsMessage message, rest)
  else if tag = 71 then (InavMessage.decode bytes).map fun (message, rest) => (.inavMessage message, rest)
  else if tag = 114 then (DollarBuySellMessage.decode bytes).map fun (message, rest) => (.dollarBuySellMessage message, rest)
  else if tag = 115 then (ShortSalesBalancesPerInstrumentMessage.decode bytes).map fun (message, rest) => (.shortSalesBalancesPerInstrumentMessage message, rest)
  else if tag = 116 then (CapitalMarketMultiplesMessage.decode bytes).map fun (message, rest) => (.capitalMarketMultiplesMessage message, rest)
  else if tag = 120 then (BenchmarkMessage.decode bytes).map fun (message, rest) => (.benchmarkMessage message, rest)
  else if tag = 122 then (CapitalizationRulesMessage.decode bytes).map fun (message, rest) => (.capitalizationRulesMessage message, rest)
  else if tag = 126 then (ClosingPriceOriginMessage.decode bytes).map fun (message, rest) => (.closingPriceOriginMessage message, rest)
  else if tag = 40 then (MutualFundsTradesMessage.decode bytes).map fun (message, rest) => (.mutualFundsTradesMessage message, rest)
  else if tag = 41 then (OpeningOfContinuousAuctionsMessage.decode bytes).map fun (message, rest) => (.openingOfContinuousAuctionsMessage message, rest)
  else if tag = 44 then (ExistenceOfBidsAtMidPriceMessage.decode bytes).map fun (message, rest) => (.existenceOfBidsAtMidPriceMessage message, rest)
  else if tag = 46 then (CatalogueOfDebtAndMetalsInstrumentsMessage.decode bytes).map fun (message, rest) => (.catalogueOfDebtAndMetalsInstrumentsMessage message, rest)
  else if tag = 48 then (CatalogSentForInstrumentsBelongingToMutualFundsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToMutualFundsMessage message, rest)
  else if tag = 54 then (WeightedAveragePriceMessage.decode bytes).map fun (message, rest) => (.weightedAveragePriceMessage message, rest)
  else if tag = 55 then (SystemEventsMessage.decode bytes).map fun (message, rest) => (.systemEventsMessage message, rest)
  else if tag = 56 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 57 then (ChangesInStatusMessage.decode bytes).map fun (message, rest) => (.changesInStatusMessage message, rest)
  else if tag = 84 then (CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage message, rest)
  else if tag = 91 then (CatalogSentForInstrumentsBelongingToCapitalTracsMessage.decode bytes).map fun (message, rest) => (.catalogSentForInstrumentsBelongingToCapitalTracsMessage message, rest)
  else if tag = 93 then (ConsolidatedInavMessage.decode bytes).map fun (message, rest) => (.consolidatedInavMessage message, rest)
  else if tag = 104 then (CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.decode bytes).map fun (message, rest) => (.catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage message, rest)
  else if tag = 105 then (ProbablePriceOfAllocationMessage.decode bytes).map fun (message, rest) => (.probablePriceOfAllocationMessage message, rest)
  else if tag = 106 then (RelationBetweenBmvbivaInstrumentsMessage.decode bytes).map fun (message, rest) => (.relationBetweenBmvbivaInstrumentsMessage message, rest)
  else if tag = 112 then (EquitiesMarketTradesMessage.decode bytes).map fun (message, rest) => (.equitiesMarketTradesMessage message, rest)
  else if tag = 113 then (ConsolidatedTradeCancellationMessage.decode bytes).map fun (message, rest) => (.consolidatedTradeCancellationMessage message, rest)
  else if tag = 92 then (PricevolumeIndicatorMessage.decode bytes).map fun (message, rest) => (.pricevolumeIndicatorMessage message, rest)
  else if tag = 107 then (ConsolidatedExecutionOfOrdersMessage.decode bytes).map fun (message, rest) => (.consolidatedExecutionOfOrdersMessage message, rest)
  else if tag = 110 then (RegistrationOfOrderMessage.decode bytes).map fun (message, rest) => (.registrationOfOrderMessage message, rest)
  else if tag = 117 then (CancellationsOfOrdersMessage.decode bytes).map fun (message, rest) => (.cancellationsOfOrdersMessage message, rest)
  else if tag = 109 then (LastQuoteMessage.decode bytes).map fun (message, rest) => (.lastQuoteMessage message, rest)
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
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | replayResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReplayResponseMessage.encode_length]
    omega
  | snapshotResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotResponseMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotCompleteMessage.encode_length]
    omega
  | eventsSystemMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EventsSystemMessage.encode_length]
    omega
  | tradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancellationMessage.encode_length]
    omega
  | statusChangesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatusChangesMessage.encode_length]
    omega
  | weightedAveragePriceSettlementPricesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, WeightedAveragePriceSettlementPricesMessage.encode_length]
    omega
  | capitalTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CapitalTradesMessage.encode_length]
    omega
  | probableAllocationPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProbableAllocationPriceMessage.encode_length]
    omega
  | continuousAuctionsBeginningMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ContinuousAuctionsBeginningMessage.encode_length]
    omega
  | middlePriceExistingQuotesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MiddlePriceExistingQuotesMessage.encode_length]
    omega
  | registryOperationsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegistryOperationsMessage.encode_length]
    omega
  | mutualFundTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MutualFundTradesMessage.encode_length]
    omega
  | tradabilityMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradabilityMessage.encode_length]
    omega
  | virtualTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, VirtualTradesMessage.encode_length]
    omega
  | orderAdditionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAdditionMessage.encode_length]
    omega
  | executionOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionOfOrdersMessage.encode_length]
    omega
  | orderCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancellationMessage.encode_length]
    omega
  | orderChangeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderChangeMessage.encode_length]
    omega
  | depthMessage inner =>
    have bound_inner := DepthMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUInt_length]
    omega
  | bestOfferMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BestOfferMessage.encode_length]
    omega
  | publicOfferingsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PublicOfferingsMessage.encode_length]
    omega
  | openInterestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpenInterestMessage.encode_length]
    omega
  | derivativesMarketTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DerivativesMarketTradesMessage.encode_length]
    omega
  | statisticsOfInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, StatisticsOfInstrumentsMessage.encode_length]
    omega
  | generalIndicesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, GeneralIndicesMessage.encode_length]
    omega
  | indicesComponentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, IndicesComponentsMessage.encode_length]
    omega
  | inavMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, InavMessage.encode_length]
    omega
  | dollarBuySellMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, DollarBuySellMessage.encode_length]
    omega
  | shortSalesBalancesPerInstrumentMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ShortSalesBalancesPerInstrumentMessage.encode_length]
    omega
  | capitalMarketMultiplesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CapitalMarketMultiplesMessage.encode_length]
    omega
  | benchmarkMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BenchmarkMessage.encode_length]
    omega
  | capitalizationRulesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CapitalizationRulesMessage.encode_length]
    omega
  | closingPriceOriginMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ClosingPriceOriginMessage.encode_length]
    omega
  | mutualFundsTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MutualFundsTradesMessage.encode_length]
    omega
  | openingOfContinuousAuctionsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OpeningOfContinuousAuctionsMessage.encode_length]
    omega
  | existenceOfBidsAtMidPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExistenceOfBidsAtMidPriceMessage.encode_length]
    omega
  | catalogueOfDebtAndMetalsInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogueOfDebtAndMetalsInstrumentsMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToMutualFundsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToMutualFundsMessage.encode_length]
    omega
  | weightedAveragePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, WeightedAveragePriceMessage.encode_length]
    omega
  | systemEventsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventsMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ReferencePriceMessage.encode_length]
    omega
  | changesInStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ChangesInStatusMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.encode_length]
    omega
  | catalogSentForInstrumentsBelongingToCapitalTracsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogSentForInstrumentsBelongingToCapitalTracsMessage.encode_length]
    omega
  | consolidatedInavMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedInavMessage.encode_length]
    omega
  | catalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.encode_length]
    omega
  | probablePriceOfAllocationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ProbablePriceOfAllocationMessage.encode_length]
    omega
  | relationBetweenBmvbivaInstrumentsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RelationBetweenBmvbivaInstrumentsMessage.encode_length]
    omega
  | equitiesMarketTradesMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquitiesMarketTradesMessage.encode_length]
    omega
  | consolidatedTradeCancellationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedTradeCancellationMessage.encode_length]
    omega
  | pricevolumeIndicatorMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, PricevolumeIndicatorMessage.encode_length]
    omega
  | consolidatedExecutionOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ConsolidatedExecutionOfOrdersMessage.encode_length]
    omega
  | registrationOfOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RegistrationOfOrderMessage.encode_length]
    omega
  | cancellationsOfOrdersMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CancellationsOfOrdersMessage.encode_length]
    omega
  | lastQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LastQuoteMessage.encode_length]
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

/-- Tcp Unit -/
structure TcpUnit where
  marketDataGroup : BitVec 8
  session : BitVec 8
  sequenceNumber : BitVec 32
  datetime : BitVec 64
  messageBlock : Bounded 1 MessageBlock
  deriving DecidableEq, Repr

namespace TcpUnit

def encodeBody (message : TcpUnit) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.messageBlock.val.length)
    ++ (encodeUInt 1 message.marketDataGroup
    ++ (encodeUInt 1 message.session
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 8 message.datetime
    ++ (encodeMany MessageBlock.encode message.messageBlock.val)))))

def decodeBody (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (totalMessages, bytes) ← decodeUInt 1 bytes
  let (marketDataGroup, bytes) ← decodeUInt 1 bytes
  let (session, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (datetime, bytes) ← decodeUInt 8 bytes
  let (messageBlock_, bytes) ← decodeMany MessageBlock.decode totalMessages.toNat bytes
  if fits_messageBlock : messageBlock_.length < 256 ^ 1 then
    pure ({ marketDataGroup, session, sequenceNumber, datetime, messageBlock := ⟨messageBlock_, fits_messageBlock⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : TcpUnit) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : TcpUnit) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : TcpUnit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : TcpUnit) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end TcpUnit

/-- Packet -/
structure Packet where
  tcpUnit : List TcpUnit
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany TcpUnit.encode message.tcpUnit

def decode (bytes : List UInt8) : Option Packet := do
  let tcpUnit ← decodeAll TcpUnit.decode bytes.length bytes
  pure { tcpUnit }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany TcpUnit.encode TcpUnit.decode TcpUnit.decode_encode TcpUnit.encode_length_pos message.tcpUnit _ (encodeMany_length_ge TcpUnit.encode TcpUnit.encode_length_pos message.tcpUnit), some_bind]
  rfl

end Packet

end Omi.BmvBmvmarketdataSnapshotIntraV11Tcp
