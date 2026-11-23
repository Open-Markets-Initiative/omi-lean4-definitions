import Wire

/-!
# National Stock Exchange of India Ltd Order Entry v6.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Cryptographic Payload is keyed on Message Length, the length framing it, and closes that frame
behind 108 fixed bytes: it is read as the arm as wide as what the frame leaves (124 being Existing
Encryption Tail, 16 bytes, 136 being New Encryption Tail, 28 bytes)

Note: St Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Trade Confirmation Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Order Entry Out Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Order Entry Short Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Security Status Change Message is selected by more than one code: each is a constructor of its
own over the one record, so the code read is the code written back

Note: Security Eligibility Indicator is a bit field set, proven as its 1 byte integer rather than
bit by bit

Note: Eligiblity Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Purpose Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Broker Eligibility Per Market is a bit field set, proven as its 2 byte integer rather than bit
by bit

Note: Security Eligible Indicator is a bit field set, proven as its 1 byte integer rather than bit
by bit

Note: System Information Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: Trade Inquiry Out Message is selected by more than one code: each is a constructor of its own
over the one record, so the code read is the code written back

Note: User Unlock Approval Rejection Message is selected by more than one code: each is a
constructor of its own over the one record, so the code read is the code written back

Note: Local Database Data is not framed: its length Message Length is not an integer it reads

Note: Server Message's body has no bound its 2 byte Message Length must fit, so every message
carries the proof its own encoding fits: the record is its body with that proof, checked as the
frame is read

License: MIT No Attribution
-/

namespace Omi.NseNsecmOrderentryNnfV66Server

/-- Inquirydata: 36 bytes -/
structure Inquirydata where
  token : BitVec 32
  auctionNumber : BitVec 16
  auctionStatus : BitVec 16
  initiatorType : BitVec 16
  totalBuy : BitVec 32
  bestBuyPrice : BitVec 32
  totalSell : BitVec 32
  bestSellPrice : BitVec 32
  auctioinPrice : BitVec 32
  auctionQuantity : BitVec 32
  settlementPeriod : BitVec 16
  deriving DecidableEq, Repr

namespace Inquirydata

def encode (message : Inquirydata) : List UInt8 :=
  encodeUInt 4 message.token
    ++ (encodeUInt 2 message.auctionNumber
    ++ (encodeUInt 2 message.auctionStatus
    ++ (encodeUInt 2 message.initiatorType
    ++ (encodeUInt 4 message.totalBuy
    ++ (encodeUInt 4 message.bestBuyPrice
    ++ (encodeUInt 4 message.totalSell
    ++ (encodeUInt 4 message.bestSellPrice
    ++ (encodeUInt 4 message.auctioinPrice
    ++ (encodeUInt 4 message.auctionQuantity
    ++ (encodeUInt 2 message.settlementPeriod))))))))))

def decode (bytes : List UInt8) : Option (Inquirydata × List UInt8) := do
  let (token, bytes) ← decodeUInt 4 bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (auctionStatus, bytes) ← decodeUInt 2 bytes
  let (initiatorType, bytes) ← decodeUInt 2 bytes
  let (totalBuy, bytes) ← decodeUInt 4 bytes
  let (bestBuyPrice, bytes) ← decodeUInt 4 bytes
  let (totalSell, bytes) ← decodeUInt 4 bytes
  let (bestSellPrice, bytes) ← decodeUInt 4 bytes
  let (auctioinPrice, bytes) ← decodeUInt 4 bytes
  let (auctionQuantity, bytes) ← decodeUInt 4 bytes
  let (settlementPeriod, bytes) ← decodeUInt 2 bytes
  pure ({ token, auctionNumber, auctionStatus, initiatorType, totalBuy, bestBuyPrice, totalSell, bestSellPrice, auctioinPrice, auctionQuantity, settlementPeriod }, bytes)

@[simp] theorem encode_length (message : Inquirydata) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Inquirydata) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Inquirydata) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Inquirydata

/-- Auction Inquiry Response Message: 182 bytes -/
structure AuctionInquiryResponseMessage where
  numberOfRecords : BitVec 16
  inquirydata : Exact 5 Inquirydata
  deriving DecidableEq, Repr

namespace AuctionInquiryResponseMessage

def encode (message : AuctionInquiryResponseMessage) : List UInt8 :=
  encodeUInt 2 message.numberOfRecords
    ++ (encodeMany Inquirydata.encode message.inquirydata.val)

def decode (bytes : List UInt8) : Option (AuctionInquiryResponseMessage × List UInt8) := do
  let (numberOfRecords, bytes) ← decodeUInt 2 bytes
  let (inquirydata_, bytes) ← decodeMany Inquirydata.decode 5 bytes
  if fits_inquirydata : inquirydata_.length = 5 then
    pure ({ numberOfRecords, inquirydata := ⟨inquirydata_, fits_inquirydata⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : AuctionInquiryResponseMessage) : (encode message).length = 182 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Inquirydata.encode 36 Inquirydata.encode_length, message.inquirydata.length_eq]

theorem encode_length_pos (message : AuctionInquiryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionInquiryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 5 Inquirydata.encode Inquirydata.decode Inquirydata.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.inquirydata.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AuctionInquiryResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AuctionInquiryResponseMessage

/-- Branch Limit: 32 bytes -/
structure BranchLimit where
  branchBuyValueLimit : Alpha 8
  reserved8 : Alpha 8
  branchSellValueLimit : Alpha 8
  secondReserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace BranchLimit

def encode (message : BranchLimit) : List UInt8 :=
  Alpha.encode message.branchBuyValueLimit
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.branchSellValueLimit
    ++ (Alpha.encode message.secondReserved8)))

def decode (bytes : List UInt8) : Option (BranchLimit × List UInt8) := do
  let (branchBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (branchSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ branchBuyValueLimit, reserved8, branchSellValueLimit, secondReserved8 }, bytes)

@[simp] theorem encode_length (message : BranchLimit) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BranchLimit) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchLimit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BranchLimit

/-- Branch Order Value Limit Update Out Message: 64 bytes -/
structure BranchOrderValueLimitUpdateOutMessage where
  brokerId : Alpha 5
  reserved25 : Alpha 25
  branch : BitVec 16
  branchLimit : BranchLimit
  deriving DecidableEq, Repr

namespace BranchOrderValueLimitUpdateOutMessage

def encode (message : BranchOrderValueLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved25
    ++ (encodeUInt 2 message.branch
    ++ (BranchLimit.encode message.branchLimit)))

def decode (bytes : List UInt8) : Option (BranchOrderValueLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved25, bytes) ← Alpha.decode 25 bytes
  let (branch, bytes) ← decodeUInt 2 bytes
  let (branchLimit, bytes) ← BranchLimit.decode bytes
  pure ({ brokerId, reserved25, branch, branchLimit }, bytes)

@[simp] theorem encode_length (message : BranchOrderValueLimitUpdateOutMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, BranchLimit.encode_length]

theorem encode_length_pos (message : BranchOrderValueLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BranchOrderValueLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [BranchLimit.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BranchOrderValueLimitUpdateOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BranchOrderValueLimitUpdateOutMessage

/-- Cancel On Logout Status Response Message: 6 bytes -/
structure CancelOnLogoutStatusResponseMessage where
  userId : BitVec 32
  coloUserBit : Alpha 1
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace CancelOnLogoutStatusResponseMessage

def encode (message : CancelOnLogoutStatusResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.coloUserBit
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (CancelOnLogoutStatusResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (coloUserBit, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, coloUserBit, reserved1 }, bytes)

@[simp] theorem encode_length (message : CancelOnLogoutStatusResponseMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOnLogoutStatusResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOnLogoutStatusResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelOnLogoutStatusResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelOnLogoutStatusResponseMessage

/-- Sec Info: 12 bytes -/
structure SecInfo where
  symbol : Alpha 10
  series : Alpha 2
  deriving DecidableEq, Repr

namespace SecInfo

def encode (message : SecInfo) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.series)

def decode (bytes : List UInt8) : Option (SecInfo × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 10 bytes
  let (series, bytes) ← Alpha.decode 2 bytes
  pure ({ symbol, series }, bytes)

@[simp] theorem encode_length (message : SecInfo) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SecInfo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecInfo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecInfo

/-- Error Response Message: 140 bytes -/
structure ErrorResponseMessage where
  secInfo : SecInfo
  errorMessage : Alpha 128
  deriving DecidableEq, Repr

namespace ErrorResponseMessage

def encode (message : ErrorResponseMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (Alpha.encode message.errorMessage)

def decode (bytes : List UInt8) : Option (ErrorResponseMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (errorMessage, bytes) ← Alpha.decode 128 bytes
  pure ({ secInfo, errorMessage }, bytes)

@[simp] theorem encode_length (message : ErrorResponseMessage) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ErrorResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ErrorResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ErrorResponseMessage

/-- Box Sign On Response Message: 12 bytes -/
structure BoxSignOnResponseMessage where
  boxId : BitVec 16
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace BoxSignOnResponseMessage

def encode (message : BoxSignOnResponseMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.reserved10)

def decode (bytes : List UInt8) : Option (BoxSignOnResponseMessage × List UInt8) := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ boxId, reserved10 }, bytes)

@[simp] theorem encode_length (message : BoxSignOnResponseMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BoxSignOnResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BoxSignOnResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BoxSignOnResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BoxSignOnResponseMessage

/-- Existing Encryption Tail: 16 bytes -/
structure ExistingEncryptionTail where
  cryptographicIv : Alpha 16
  deriving DecidableEq, Repr

namespace ExistingEncryptionTail

def encode (message : ExistingEncryptionTail) : List UInt8 :=
  Alpha.encode message.cryptographicIv

def decode (bytes : List UInt8) : Option (ExistingEncryptionTail × List UInt8) := do
  let (cryptographicIv, bytes) ← Alpha.decode 16 bytes
  pure ({ cryptographicIv }, bytes)

@[simp] theorem encode_length (message : ExistingEncryptionTail) : (encode message).length = 16 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ExistingEncryptionTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExistingEncryptionTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExistingEncryptionTail

/-- New Encryption Tail: 28 bytes -/
structure NewEncryptionTail where
  staticCryptographicIv : Alpha 8
  dynamicCryptographicIv : BitVec 64
  cryptographicAdditionalKey : Alpha 12
  deriving DecidableEq, Repr

namespace NewEncryptionTail

def encode (message : NewEncryptionTail) : List UInt8 :=
  Alpha.encode message.staticCryptographicIv
    ++ (encodeUInt 8 message.dynamicCryptographicIv
    ++ (Alpha.encode message.cryptographicAdditionalKey))

def decode (bytes : List UInt8) : Option (NewEncryptionTail × List UInt8) := do
  let (staticCryptographicIv, bytes) ← Alpha.decode 8 bytes
  let (dynamicCryptographicIv, bytes) ← decodeUInt 8 bytes
  let (cryptographicAdditionalKey, bytes) ← Alpha.decode 12 bytes
  pure ({ staticCryptographicIv, dynamicCryptographicIv, cryptographicAdditionalKey }, bytes)

@[simp] theorem encode_length (message : NewEncryptionTail) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewEncryptionTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewEncryptionTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewEncryptionTail

/-- Gateway Router Response Message -/
structure GatewayRouterResponseMessage where
  boxId : BitVec 16
  brokerId : Alpha 5
  filler : Alpha 1
  ipAddress : Alpha 16
  port : BitVec 32
  sessionKey : Alpha 8
  cryptographicKey : Alpha 32
  cryptographicPayload : ExistingEncryptionTail ⊕ (NewEncryptionTail)
  deriving DecidableEq, Repr

namespace GatewayRouterResponseMessage

def encode (message : GatewayRouterResponseMessage) : List UInt8 :=
  encodeUInt 2 message.boxId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.filler
    ++ (Alpha.encode message.ipAddress
    ++ (encodeUInt 4 message.port
    ++ (Alpha.encode message.sessionKey
    ++ (Alpha.encode message.cryptographicKey
    ++ (encodeEither ExistingEncryptionTail.encode (NewEncryptionTail.encode) message.cryptographicPayload)))))))

def decode (bytes : List UInt8) : Option GatewayRouterResponseMessage := do
  let (boxId, bytes) ← decodeUInt 2 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (ipAddress, bytes) ← Alpha.decode 16 bytes
  let (port, bytes) ← decodeUInt 4 bytes
  let (sessionKey, bytes) ← Alpha.decode 8 bytes
  let (cryptographicKey, bytes) ← Alpha.decode 32 bytes
  let cryptographicPayload ← decodeByWidth 16 (decodeWhole ExistingEncryptionTail.decode) ((decodeWhole NewEncryptionTail.decode)) bytes
  pure { boxId, brokerId, filler, ipAddress, port, sessionKey, cryptographicKey, cryptographicPayload }

theorem encode_length_pos (message : GatewayRouterResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : GatewayRouterResponseMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeByWidth_encodeEither ExistingEncryptionTail.encode (decodeWhole ExistingEncryptionTail.decode) (NewEncryptionTail.encode) ((decodeWhole NewEncryptionTail.decode)) 16 ExistingEncryptionTail.encode_length (by intro item; simp [NewEncryptionTail.encode_length]) (decodeWhole_encode ExistingEncryptionTail.encode ExistingEncryptionTail.decode ExistingEncryptionTail.decode_encode) ((decodeWhole_encode NewEncryptionTail.encode NewEncryptionTail.decode NewEncryptionTail.decode_encode)), some_bind]
  rfl

end GatewayRouterResponseMessage

/-- Control Message To Trader Message: 250 bytes -/
structure ControlMessageToTraderMessage where
  traderId : BitVec 32
  actionCode : Alpha 3
  reserved1 : Alpha 1
  msgLength : BitVec 16
  msg : Alpha 240
  deriving DecidableEq, Repr

namespace ControlMessageToTraderMessage

def encode (message : ControlMessageToTraderMessage) : List UInt8 :=
  encodeUInt 4 message.traderId
    ++ (Alpha.encode message.actionCode
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.msgLength
    ++ (Alpha.encode message.msg))))

def decode (bytes : List UInt8) : Option (ControlMessageToTraderMessage × List UInt8) := do
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (actionCode, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (msgLength, bytes) ← decodeUInt 2 bytes
  let (msg, bytes) ← Alpha.decode 240 bytes
  pure ({ traderId, actionCode, reserved1, msgLength, msg }, bytes)

@[simp] theorem encode_length (message : ControlMessageToTraderMessage) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ControlMessageToTraderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ControlMessageToTraderMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ControlMessageToTraderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ControlMessageToTraderMessage

/-- Trade Confirmation Message: 188 bytes -/
structure TradeConfirmationMessage where
  responseOrderNumber : Alpha 8
  brokerId : Alpha 5
  reserved1 : Alpha 1
  traderNum : BitVec 32
  accountNum : Alpha 10
  buySell : BitVec 16
  originalVol : BitVec 32
  disclosedVol : BitVec 32
  remainingVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  price : BitVec 32
  stOrderFlags : BitVec 16
  gtd : BitVec 32
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  volFilledToday : BitVec 32
  activityType : Alpha 2
  activityTime : BitVec 32
  opOrderNumber : Alpha 8
  opBrokerId : Alpha 5
  secInfo : SecInfo
  secondReserved1 : Alpha 1
  bookType : BitVec 16
  newVolume : BitVec 32
  proClient : BitVec 16
  pan : Alpha 10
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
    ++ (encodeUInt 4 message.traderNum
    ++ (Alpha.encode message.accountNum
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.originalVol
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.remainingVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 4 message.gtd
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 4 message.volFilledToday
    ++ (Alpha.encode message.activityType
    ++ (encodeUInt 4 message.activityTime
    ++ (Alpha.encode message.opOrderNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (SecInfo.encode message.secInfo
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 4 message.newVolume
    ++ (encodeUInt 2 message.proClient
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeConfirmationMessage × List UInt8) := do
  let (responseOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (traderNum, bytes) ← decodeUInt 4 bytes
  let (accountNum, bytes) ← Alpha.decode 10 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (originalVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (remainingVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (gtd, bytes) ← decodeUInt 4 bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (volFilledToday, bytes) ← decodeUInt 4 bytes
  let (activityType, bytes) ← Alpha.decode 2 bytes
  let (activityTime, bytes) ← decodeUInt 4 bytes
  let (opOrderNumber, bytes) ← Alpha.decode 8 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ responseOrderNumber, brokerId, reserved1, traderNum, accountNum, buySell, originalVol, disclosedVol, remainingVol, disclosedVolRemaining, price, stOrderFlags, gtd, fillNumber, fillQty, fillPrice, volFilledToday, activityType, activityTime, opOrderNumber, opBrokerId, secInfo, secondReserved1, bookType, newVolume, proClient, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : TradeConfirmationMessage) : (encode message).length = 188 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SecInfo.encode_length]

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
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeConfirmationMessage

/-- Order Entry Out Message: 250 bytes -/
structure OrderEntryOutMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : Alpha 1
  filler9 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  secInfo : SecInfo
  auctionNumber : BitVec 16
  opBrokerId : Alpha 5
  suspended : Alpha 1
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 25
  settlor : Alpha 12
  proClient : BitVec 16
  settlementType : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  secondReserved4 : Alpha 4
  pan : Alpha 10
  algoId : BitVec 32
  reserved2 : Alpha 2
  lastActivityReference : BitVec 64
  reserved52 : Alpha 52
  deriving DecidableEq, Repr

namespace OrderEntryOutMessage

def encode (message : OrderEntryOutMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modCxlBy
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementType
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.secondReserved4
    ++ (Alpha.encode message.pan
    ++ (encodeUInt 4 message.algoId
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 8 message.lastActivityReference
    ++ (Alpha.encode message.reserved52))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderEntryOutMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 25 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  let (pan, bytes) ← Alpha.decode 10 bytes
  let (algoId, bytes) ← decodeUInt 4 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (lastActivityReference, bytes) ← decodeUInt 8 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, settlor, proClient, settlementType, nnfField, execTimeStamp, secondReserved4, pan, algoId, reserved2, lastActivityReference, reserved52 }, bytes)

@[simp] theorem encode_length (message : OrderEntryOutMessage) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderEntryOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderEntryOutMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderEntryOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderEntryOutMessage

/-- Order Entry Short Message: 174 bytes -/
structure OrderEntryShortMessage where
  participantType : Alpha 1
  reserved1 : Alpha 1
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  modCxlBy : Alpha 1
  filler9 : Alpha 1
  reasonCode : BitVec 16
  reserved4 : Alpha 4
  secInfo : SecInfo
  auctionNumber : BitVec 16
  opBrokerId : Alpha 5
  suspended : Alpha 1
  orderNumber : Alpha 8
  accountNumber : Alpha 10
  bookType : BitVec 16
  buySell : BitVec 16
  disclosedVol : BitVec 32
  disclosedVolRemaining : BitVec 32
  totalVolRemaining : BitVec 32
  volume : BitVec 32
  volumeFilledToday : BitVec 32
  price : BitVec 32
  triggerPrice : BitVec 32
  goodTillDate : BitVec 32
  entryDateTime : BitVec 32
  minFillAon : BitVec 32
  lastModified : BitVec 32
  stOrderFlags : BitVec 16
  branchId : BitVec 16
  traderId : BitVec 32
  brokerId : Alpha 5
  oeRemarks : Alpha 25
  settlor : Alpha 12
  proClient : BitVec 16
  settlementType : BitVec 16
  nnfField : Alpha 8
  execTimeStamp : Alpha 8
  secondReserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace OrderEntryShortMessage

def encode (message : OrderEntryShortMessage) : List UInt8 :=
  Alpha.encode message.participantType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (Alpha.encode message.modCxlBy
    ++ (Alpha.encode message.filler9
    ++ (encodeUInt 2 message.reasonCode
    ++ (Alpha.encode message.reserved4
    ++ (SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.auctionNumber
    ++ (Alpha.encode message.opBrokerId
    ++ (Alpha.encode message.suspended
    ++ (Alpha.encode message.orderNumber
    ++ (Alpha.encode message.accountNumber
    ++ (encodeUInt 2 message.bookType
    ++ (encodeUInt 2 message.buySell
    ++ (encodeUInt 4 message.disclosedVol
    ++ (encodeUInt 4 message.disclosedVolRemaining
    ++ (encodeUInt 4 message.totalVolRemaining
    ++ (encodeUInt 4 message.volume
    ++ (encodeUInt 4 message.volumeFilledToday
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.triggerPrice
    ++ (encodeUInt 4 message.goodTillDate
    ++ (encodeUInt 4 message.entryDateTime
    ++ (encodeUInt 4 message.minFillAon
    ++ (encodeUInt 4 message.lastModified
    ++ (encodeUInt 2 message.stOrderFlags
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.traderId
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.oeRemarks
    ++ (Alpha.encode message.settlor
    ++ (encodeUInt 2 message.proClient
    ++ (encodeUInt 2 message.settlementType
    ++ (Alpha.encode message.nnfField
    ++ (Alpha.encode message.execTimeStamp
    ++ (Alpha.encode message.secondReserved4)))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderEntryShortMessage × List UInt8) := do
  let (participantType, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (modCxlBy, bytes) ← Alpha.decode 1 bytes
  let (filler9, bytes) ← Alpha.decode 1 bytes
  let (reasonCode, bytes) ← decodeUInt 2 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (auctionNumber, bytes) ← decodeUInt 2 bytes
  let (opBrokerId, bytes) ← Alpha.decode 5 bytes
  let (suspended, bytes) ← Alpha.decode 1 bytes
  let (orderNumber, bytes) ← Alpha.decode 8 bytes
  let (accountNumber, bytes) ← Alpha.decode 10 bytes
  let (bookType, bytes) ← decodeUInt 2 bytes
  let (buySell, bytes) ← decodeUInt 2 bytes
  let (disclosedVol, bytes) ← decodeUInt 4 bytes
  let (disclosedVolRemaining, bytes) ← decodeUInt 4 bytes
  let (totalVolRemaining, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (volumeFilledToday, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (triggerPrice, bytes) ← decodeUInt 4 bytes
  let (goodTillDate, bytes) ← decodeUInt 4 bytes
  let (entryDateTime, bytes) ← decodeUInt 4 bytes
  let (minFillAon, bytes) ← decodeUInt 4 bytes
  let (lastModified, bytes) ← decodeUInt 4 bytes
  let (stOrderFlags, bytes) ← decodeUInt 2 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (oeRemarks, bytes) ← Alpha.decode 25 bytes
  let (settlor, bytes) ← Alpha.decode 12 bytes
  let (proClient, bytes) ← decodeUInt 2 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (nnfField, bytes) ← Alpha.decode 8 bytes
  let (execTimeStamp, bytes) ← Alpha.decode 8 bytes
  let (secondReserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ participantType, reserved1, competitorPeriod, solicitorPeriod, modCxlBy, filler9, reasonCode, reserved4, secInfo, auctionNumber, opBrokerId, suspended, orderNumber, accountNumber, bookType, buySell, disclosedVol, disclosedVolRemaining, totalVolRemaining, volume, volumeFilledToday, price, triggerPrice, goodTillDate, entryDateTime, minFillAon, lastModified, stOrderFlags, branchId, traderId, brokerId, oeRemarks, settlor, proClient, settlementType, nnfField, execTimeStamp, secondReserved4 }, bytes)

@[simp] theorem encode_length (message : OrderEntryShortMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, SecInfo.encode_length]

theorem encode_length_pos (message : OrderEntryShortMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderEntryShortMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderEntryShortMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderEntryShortMessage

/-- Order Limit Update Out Message: 28 bytes -/
structure OrderLimitUpdateOutMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  userId : BitVec 32
  orderQtyLimit : Alpha 8
  orderValLimit : Alpha 8
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace OrderLimitUpdateOutMessage

def encode (message : OrderLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 4 message.userId
    ++ (Alpha.encode message.orderQtyLimit
    ++ (Alpha.encode message.orderValLimit
    ++ (Alpha.encode message.reserved2)))))

def decode (bytes : List UInt8) : Option (OrderLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (orderQtyLimit, bytes) ← Alpha.decode 8 bytes
  let (orderValLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ brokerId, reserved1, userId, orderQtyLimit, orderValLimit, reserved2 }, bytes)

@[simp] theorem encode_length (message : OrderLimitUpdateOutMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderLimitUpdateOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderLimitUpdateOutMessage

/-- Password Reset Out Message: 18 bytes -/
structure PasswordResetOutMessage where
  userId : BitVec 32
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace PasswordResetOutMessage

def encode (message : PasswordResetOutMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.reserved14)

def decode (bytes : List UInt8) : Option (PasswordResetOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ userId, reserved14 }, bytes)

@[simp] theorem encode_length (message : PasswordResetOutMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PasswordResetOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PasswordResetOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PasswordResetOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PasswordResetOutMessage

/-- Security Status Per Market: 2 bytes -/
structure SecurityStatusPerMarket where
  status : BitVec 16
  deriving DecidableEq, Repr

namespace SecurityStatusPerMarket

def encode (message : SecurityStatusPerMarket) : List UInt8 :=
  encodeUInt 2 message.status

def decode (bytes : List UInt8) : Option (SecurityStatusPerMarket × List UInt8) := do
  let (status, bytes) ← decodeUInt 2 bytes
  pure ({ status }, bytes)

@[simp] theorem encode_length (message : SecurityStatusPerMarket) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecurityStatusPerMarket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusPerMarket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecurityStatusPerMarket

/-- Token And Eligibility: 16 bytes -/
structure TokenAndEligibility where
  token : BitVec 32
  securityStatusPerMarket : Exact 6 SecurityStatusPerMarket
  deriving DecidableEq, Repr

namespace TokenAndEligibility

def encode (message : TokenAndEligibility) : List UInt8 :=
  encodeUInt 4 message.token
    ++ (encodeMany SecurityStatusPerMarket.encode message.securityStatusPerMarket.val)

def decode (bytes : List UInt8) : Option (TokenAndEligibility × List UInt8) := do
  let (token, bytes) ← decodeUInt 4 bytes
  let (securityStatusPerMarket_, bytes) ← decodeMany SecurityStatusPerMarket.decode 6 bytes
  if fits_securityStatusPerMarket : securityStatusPerMarket_.length = 6 then
    pure ({ token, securityStatusPerMarket := ⟨securityStatusPerMarket_, fits_securityStatusPerMarket⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : TokenAndEligibility) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const SecurityStatusPerMarket.encode 2 SecurityStatusPerMarket.encode_length, message.securityStatusPerMarket.length_eq]

theorem encode_length_pos (message : TokenAndEligibility) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TokenAndEligibility) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 6 SecurityStatusPerMarket.encode SecurityStatusPerMarket.decode SecurityStatusPerMarket.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusPerMarket.length_eq]
  rfl

end TokenAndEligibility

/-- Security Status Change Message: 402 bytes -/
structure SecurityStatusChangeMessage where
  numberOfRecords : BitVec 16
  tokenAndEligibility : Exact 25 TokenAndEligibility
  deriving DecidableEq, Repr

namespace SecurityStatusChangeMessage

def encode (message : SecurityStatusChangeMessage) : List UInt8 :=
  encodeUInt 2 message.numberOfRecords
    ++ (encodeMany TokenAndEligibility.encode message.tokenAndEligibility.val)

def decode (bytes : List UInt8) : Option (SecurityStatusChangeMessage × List UInt8) := do
  let (numberOfRecords, bytes) ← decodeUInt 2 bytes
  let (tokenAndEligibility_, bytes) ← decodeMany TokenAndEligibility.decode 25 bytes
  if fits_tokenAndEligibility : tokenAndEligibility_.length = 25 then
    pure ({ numberOfRecords, tokenAndEligibility := ⟨tokenAndEligibility_, fits_tokenAndEligibility⟩ }, bytes)
  else none

@[simp] theorem encode_length (message : SecurityStatusChangeMessage) : (encode message).length = 402 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const TokenAndEligibility.encode 16 TokenAndEligibility.encode_length, message.tokenAndEligibility.length_eq]

theorem encode_length_pos (message : SecurityStatusChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_exact 25 TokenAndEligibility.encode TokenAndEligibility.decode TokenAndEligibility.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tokenAndEligibility.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SecurityStatusChangeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SecurityStatusChangeMessage

/-- Secuirity Eligibility Per Market: 4 bytes -/
structure SecuirityEligibilityPerMarket where
  securityEligibilityIndicator : BitVec 8
  reserved1 : Alpha 1
  status : BitVec 16
  deriving DecidableEq, Repr

namespace SecuirityEligibilityPerMarket

def encode (message : SecuirityEligibilityPerMarket) : List UInt8 :=
  encodeUIntLE 1 message.securityEligibilityIndicator
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.status))

def decode (bytes : List UInt8) : Option (SecuirityEligibilityPerMarket × List UInt8) := do
  let (securityEligibilityIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (status, bytes) ← decodeUInt 2 bytes
  pure ({ securityEligibilityIndicator, reserved1, status }, bytes)

@[simp] theorem encode_length (message : SecuirityEligibilityPerMarket) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SecuirityEligibilityPerMarket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecuirityEligibilityPerMarket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecuirityEligibilityPerMarket

/-- Eligiblity Indicators: 2 bytes -/
structure EligiblityIndicators where
  eligiblityIndicator : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace EligiblityIndicators

def encode (message : EligiblityIndicators) : List UInt8 :=
  encodeUIntLE 1 message.eligiblityIndicator
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (EligiblityIndicators × List UInt8) := do
  let (eligiblityIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ eligiblityIndicator, reserved1 }, bytes)

@[simp] theorem encode_length (message : EligiblityIndicators) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EligiblityIndicators) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EligiblityIndicators) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EligiblityIndicators

/-- Purpose: 2 bytes -/
structure Purpose where
  purposeIndicator : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace Purpose

def encode (message : Purpose) : List UInt8 :=
  encodeUIntLE 1 message.purposeIndicator
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (Purpose × List UInt8) := do
  let (purposeIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ purposeIndicator, reserved1 }, bytes)

@[simp] theorem encode_length (message : Purpose) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : Purpose) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Purpose) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end Purpose

/-- Security Master Change Message: 220 bytes -/
structure SecurityMasterChangeMessage where
  token : BitVec 32
  secInfo : SecInfo
  instrumentType : BitVec 16
  permittedToTrade : BitVec 16
  issuedCapital : Alpha 8
  settlementType : BitVec 16
  freezePercent : BitVec 16
  creditRating : Alpha 19
  reserved1 : Alpha 1
  secuirityEligibilityPerMarket : Exact 6 SecuirityEligibilityPerMarket
  survInd : BitVec 16
  issueStartDate : BitVec 32
  interestPaymentDate : BitVec 32
  issueMaturityDate : BitVec 32
  boardLotQuantity : BitVec 32
  tickSize : BitVec 32
  name : Alpha 25
  secondReserved1 : Alpha 1
  listingDate : BitVec 32
  expulsionDate : BitVec 32
  reAdmissionDate : BitVec 32
  recordDate : BitVec 32
  expiryDate : BitVec 32
  noDeliveryStartDate : BitVec 32
  noDeliveryEndDate : BitVec 32
  eligiblityIndicators : EligiblityIndicators
  bookClosureStartDate : BitVec 32
  bookClosureEndDate : BitVec 32
  purpose : Purpose
  localUpdateDateTime : BitVec 32
  deleteFlag : Alpha 1
  remark : Alpha 25
  faceValue : BitVec 32
  isinNumber : Alpha 12
  mktMakerSpread : BitVec 32
  mktMakerMinQty : BitVec 32
  callAuction1Flag : BitVec 16
  deriving DecidableEq, Repr

namespace SecurityMasterChangeMessage

def encode (message : SecurityMasterChangeMessage) : List UInt8 :=
  encodeUInt 4 message.token
    ++ (SecInfo.encode message.secInfo
    ++ (encodeUInt 2 message.instrumentType
    ++ (encodeUInt 2 message.permittedToTrade
    ++ (Alpha.encode message.issuedCapital
    ++ (encodeUInt 2 message.settlementType
    ++ (encodeUInt 2 message.freezePercent
    ++ (Alpha.encode message.creditRating
    ++ (Alpha.encode message.reserved1
    ++ (encodeMany SecuirityEligibilityPerMarket.encode message.secuirityEligibilityPerMarket.val
    ++ (encodeUInt 2 message.survInd
    ++ (encodeUInt 4 message.issueStartDate
    ++ (encodeUInt 4 message.interestPaymentDate
    ++ (encodeUInt 4 message.issueMaturityDate
    ++ (encodeUInt 4 message.boardLotQuantity
    ++ (encodeUInt 4 message.tickSize
    ++ (Alpha.encode message.name
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 4 message.listingDate
    ++ (encodeUInt 4 message.expulsionDate
    ++ (encodeUInt 4 message.reAdmissionDate
    ++ (encodeUInt 4 message.recordDate
    ++ (encodeUInt 4 message.expiryDate
    ++ (encodeUInt 4 message.noDeliveryStartDate
    ++ (encodeUInt 4 message.noDeliveryEndDate
    ++ (EligiblityIndicators.encode message.eligiblityIndicators
    ++ (encodeUInt 4 message.bookClosureStartDate
    ++ (encodeUInt 4 message.bookClosureEndDate
    ++ (Purpose.encode message.purpose
    ++ (encodeUInt 4 message.localUpdateDateTime
    ++ (Alpha.encode message.deleteFlag
    ++ (Alpha.encode message.remark
    ++ (encodeUInt 4 message.faceValue
    ++ (Alpha.encode message.isinNumber
    ++ (encodeUInt 4 message.mktMakerSpread
    ++ (encodeUInt 4 message.mktMakerMinQty
    ++ (encodeUInt 2 message.callAuction1Flag))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityMasterChangeMessage × List UInt8) := do
  let (token, bytes) ← decodeUInt 4 bytes
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (instrumentType, bytes) ← decodeUInt 2 bytes
  let (permittedToTrade, bytes) ← decodeUInt 2 bytes
  let (issuedCapital, bytes) ← Alpha.decode 8 bytes
  let (settlementType, bytes) ← decodeUInt 2 bytes
  let (freezePercent, bytes) ← decodeUInt 2 bytes
  let (creditRating, bytes) ← Alpha.decode 19 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (secuirityEligibilityPerMarket_, bytes) ← decodeMany SecuirityEligibilityPerMarket.decode 6 bytes
  let (survInd, bytes) ← decodeUInt 2 bytes
  let (issueStartDate, bytes) ← decodeUInt 4 bytes
  let (interestPaymentDate, bytes) ← decodeUInt 4 bytes
  let (issueMaturityDate, bytes) ← decodeUInt 4 bytes
  let (boardLotQuantity, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 4 bytes
  let (name, bytes) ← Alpha.decode 25 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (listingDate, bytes) ← decodeUInt 4 bytes
  let (expulsionDate, bytes) ← decodeUInt 4 bytes
  let (reAdmissionDate, bytes) ← decodeUInt 4 bytes
  let (recordDate, bytes) ← decodeUInt 4 bytes
  let (expiryDate, bytes) ← decodeUInt 4 bytes
  let (noDeliveryStartDate, bytes) ← decodeUInt 4 bytes
  let (noDeliveryEndDate, bytes) ← decodeUInt 4 bytes
  let (eligiblityIndicators, bytes) ← EligiblityIndicators.decode bytes
  let (bookClosureStartDate, bytes) ← decodeUInt 4 bytes
  let (bookClosureEndDate, bytes) ← decodeUInt 4 bytes
  let (purpose, bytes) ← Purpose.decode bytes
  let (localUpdateDateTime, bytes) ← decodeUInt 4 bytes
  let (deleteFlag, bytes) ← Alpha.decode 1 bytes
  let (remark, bytes) ← Alpha.decode 25 bytes
  let (faceValue, bytes) ← decodeUInt 4 bytes
  let (isinNumber, bytes) ← Alpha.decode 12 bytes
  let (mktMakerSpread, bytes) ← decodeUInt 4 bytes
  let (mktMakerMinQty, bytes) ← decodeUInt 4 bytes
  let (callAuction1Flag, bytes) ← decodeUInt 2 bytes
  if fits_secuirityEligibilityPerMarket : secuirityEligibilityPerMarket_.length = 6 then
    pure ({ token, secInfo, instrumentType, permittedToTrade, issuedCapital, settlementType, freezePercent, creditRating, reserved1, secuirityEligibilityPerMarket := ⟨secuirityEligibilityPerMarket_, fits_secuirityEligibilityPerMarket⟩, survInd, issueStartDate, interestPaymentDate, issueMaturityDate, boardLotQuantity, tickSize, name, secondReserved1, listingDate, expulsionDate, reAdmissionDate, recordDate, expiryDate, noDeliveryStartDate, noDeliveryEndDate, eligiblityIndicators, bookClosureStartDate, bookClosureEndDate, purpose, localUpdateDateTime, deleteFlag, remark, faceValue, isinNumber, mktMakerSpread, mktMakerMinQty, callAuction1Flag }, bytes)
  else none

@[simp] theorem encode_length (message : SecurityMasterChangeMessage) : (encode message).length = 220 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SecInfo.encode_length, Alpha.encode_length, encodeMany_length_const SecuirityEligibilityPerMarket.encode 4 SecuirityEligibilityPerMarket.encode_length, message.secuirityEligibilityPerMarket.length_eq, EligiblityIndicators.encode_length, Purpose.encode_length]

theorem encode_length_pos (message : SecurityMasterChangeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SecurityMasterChangeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_exact 6 SecuirityEligibilityPerMarket.encode SecuirityEligibilityPerMarket.decode SecuirityEligibilityPerMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, EligiblityIndicators.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Purpose.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.secuirityEligibilityPerMarket.length_eq]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SecurityMasterChangeMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SecurityMasterChangeMessage

/-- Sign On Request Out Message: 236 bytes -/
structure SignOnRequestOutMessage where
  userId : BitVec 32
  reserved8 : Alpha 8
  password : Alpha 8
  secondReserved8 : Alpha 8
  newPassword : Alpha 8
  traderName : Alpha 26
  lastPasswordChangeDateTime : BitVec 32
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branchId : BitVec 16
  versionNumber : BitVec 32
  reserved56 : Alpha 56
  userType : BitVec 16
  sequenceNumber : Alpha 8
  workstationNumber : Alpha 14
  brokerStatus : Alpha 1
  showIndex : Alpha 1
  brokerEligibilityPerMarket : BitVec 16
  brokerName : Alpha 26
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
    ++ (encodeUInt 4 message.lastPasswordChangeDateTime
    ++ (Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branchId
    ++ (encodeUInt 4 message.versionNumber
    ++ (Alpha.encode message.reserved56
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.workstationNumber
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.showIndex
    ++ (encodeUInt 2 message.brokerEligibilityPerMarket
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SignOnRequestOutMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (password, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (newPassword, bytes) ← Alpha.decode 8 bytes
  let (traderName, bytes) ← Alpha.decode 26 bytes
  let (lastPasswordChangeDateTime, bytes) ← decodeUInt 4 bytes
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branchId, bytes) ← decodeUInt 2 bytes
  let (versionNumber, bytes) ← decodeUInt 4 bytes
  let (reserved56, bytes) ← Alpha.decode 56 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (workstationNumber, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (showIndex, bytes) ← Alpha.decode 1 bytes
  let (brokerEligibilityPerMarket, bytes) ← decodeUInt 2 bytes
  let (brokerName, bytes) ← Alpha.decode 26 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDateTime, brokerId, reserved1, branchId, versionNumber, reserved56, userType, sequenceNumber, workstationNumber, brokerStatus, showIndex, brokerEligibilityPerMarket, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnRequestOutMessage) : (encode message).length = 236 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnRequestOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SignOnRequestOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SignOnRequestOutMessage

/-- Sign On Response Message: 236 bytes -/
structure SignOnResponseMessage where
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
  endTime : BitVec 32
  reserved52 : Alpha 52
  userType : BitVec 16
  sequenceNumber : Alpha 8
  reserved14 : Alpha 14
  brokerStatus : Alpha 1
  secondReserved1 : Alpha 1
  brokerEligibilityPerMarket : BitVec 16
  brokerName : Alpha 26
  reserved16 : Alpha 16
  secondReserved16 : Alpha 16
  thirdReserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SignOnResponseMessage

def encode (message : SignOnResponseMessage) : List UInt8 :=
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
    ++ (encodeUInt 4 message.endTime
    ++ (Alpha.encode message.reserved52
    ++ (encodeUInt 2 message.userType
    ++ (Alpha.encode message.sequenceNumber
    ++ (Alpha.encode message.reserved14
    ++ (Alpha.encode message.brokerStatus
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUInt 2 message.brokerEligibilityPerMarket
    ++ (Alpha.encode message.brokerName
    ++ (Alpha.encode message.reserved16
    ++ (Alpha.encode message.secondReserved16
    ++ (Alpha.encode message.thirdReserved16))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SignOnResponseMessage × List UInt8) := do
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
  let (endTime, bytes) ← decodeUInt 4 bytes
  let (reserved52, bytes) ← Alpha.decode 52 bytes
  let (userType, bytes) ← decodeUInt 2 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 8 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  let (brokerStatus, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (brokerEligibilityPerMarket, bytes) ← decodeUInt 2 bytes
  let (brokerName, bytes) ← Alpha.decode 26 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (secondReserved16, bytes) ← Alpha.decode 16 bytes
  let (thirdReserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ userId, reserved8, password, secondReserved8, newPassword, traderName, lastPasswordChangeDate, brokerId, reserved1, branchId, versionNumber, endTime, reserved52, userType, sequenceNumber, reserved14, brokerStatus, secondReserved1, brokerEligibilityPerMarket, brokerName, reserved16, secondReserved16, thirdReserved16 }, bytes)

@[simp] theorem encode_length (message : SignOnResponseMessage) : (encode message).length = 236 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SignOnResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SignOnResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SignOnResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SignOnResponseMessage

/-- Security Eligible Indicators: 2 bytes -/
structure SecurityEligibleIndicators where
  securityEligibleIndicator : BitVec 8
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace SecurityEligibleIndicators

def encode (message : SecurityEligibleIndicators) : List UInt8 :=
  encodeUIntLE 1 message.securityEligibleIndicator
    ++ (Alpha.encode message.reserved1)

def decode (bytes : List UInt8) : Option (SecurityEligibleIndicators × List UInt8) := do
  let (securityEligibleIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ securityEligibleIndicator, reserved1 }, bytes)

@[simp] theorem encode_length (message : SecurityEligibleIndicators) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityEligibleIndicators) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityEligibleIndicators) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityEligibleIndicators

/-- System Information Message: 54 bytes -/
structure SystemInformationMessage where
  normal : BitVec 16
  oddlot : BitVec 16
  spot : BitVec 16
  auction : BitVec 16
  callAuction1 : BitVec 16
  callAuction2 : BitVec 16
  marketIndex : BitVec 32
  defaultSettlementPeriod : BitVec 16
  secondDefaultSettlementPeriod : BitVec 16
  thirdDefaultSettlementPeriod : BitVec 16
  competitorPeriod : BitVec 16
  solicitorPeriod : BitVec 16
  warningPercent : BitVec 16
  volumeFreezePercent : BitVec 16
  reserved2 : Alpha 2
  terminalIdleTime : BitVec 16
  boardLotQuantity : BitVec 32
  tickSize : BitVec 32
  maximumGtcDays : BitVec 16
  securityEligibleIndicators : SecurityEligibleIndicators
  disclosedQuantityPercentAllowed : BitVec 16
  reserved6 : Alpha 6
  deriving DecidableEq, Repr

namespace SystemInformationMessage

def encode (message : SystemInformationMessage) : List UInt8 :=
  encodeUInt 2 message.normal
    ++ (encodeUInt 2 message.oddlot
    ++ (encodeUInt 2 message.spot
    ++ (encodeUInt 2 message.auction
    ++ (encodeUInt 2 message.callAuction1
    ++ (encodeUInt 2 message.callAuction2
    ++ (encodeUInt 4 message.marketIndex
    ++ (encodeUInt 2 message.defaultSettlementPeriod
    ++ (encodeUInt 2 message.secondDefaultSettlementPeriod
    ++ (encodeUInt 2 message.thirdDefaultSettlementPeriod
    ++ (encodeUInt 2 message.competitorPeriod
    ++ (encodeUInt 2 message.solicitorPeriod
    ++ (encodeUInt 2 message.warningPercent
    ++ (encodeUInt 2 message.volumeFreezePercent
    ++ (Alpha.encode message.reserved2
    ++ (encodeUInt 2 message.terminalIdleTime
    ++ (encodeUInt 4 message.boardLotQuantity
    ++ (encodeUInt 4 message.tickSize
    ++ (encodeUInt 2 message.maximumGtcDays
    ++ (SecurityEligibleIndicators.encode message.securityEligibleIndicators
    ++ (encodeUInt 2 message.disclosedQuantityPercentAllowed
    ++ (Alpha.encode message.reserved6)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SystemInformationMessage × List UInt8) := do
  let (normal, bytes) ← decodeUInt 2 bytes
  let (oddlot, bytes) ← decodeUInt 2 bytes
  let (spot, bytes) ← decodeUInt 2 bytes
  let (auction, bytes) ← decodeUInt 2 bytes
  let (callAuction1, bytes) ← decodeUInt 2 bytes
  let (callAuction2, bytes) ← decodeUInt 2 bytes
  let (marketIndex, bytes) ← decodeUInt 4 bytes
  let (defaultSettlementPeriod, bytes) ← decodeUInt 2 bytes
  let (secondDefaultSettlementPeriod, bytes) ← decodeUInt 2 bytes
  let (thirdDefaultSettlementPeriod, bytes) ← decodeUInt 2 bytes
  let (competitorPeriod, bytes) ← decodeUInt 2 bytes
  let (solicitorPeriod, bytes) ← decodeUInt 2 bytes
  let (warningPercent, bytes) ← decodeUInt 2 bytes
  let (volumeFreezePercent, bytes) ← decodeUInt 2 bytes
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (terminalIdleTime, bytes) ← decodeUInt 2 bytes
  let (boardLotQuantity, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 4 bytes
  let (maximumGtcDays, bytes) ← decodeUInt 2 bytes
  let (securityEligibleIndicators, bytes) ← SecurityEligibleIndicators.decode bytes
  let (disclosedQuantityPercentAllowed, bytes) ← decodeUInt 2 bytes
  let (reserved6, bytes) ← Alpha.decode 6 bytes
  pure ({ normal, oddlot, spot, auction, callAuction1, callAuction2, marketIndex, defaultSettlementPeriod, secondDefaultSettlementPeriod, thirdDefaultSettlementPeriod, competitorPeriod, solicitorPeriod, warningPercent, volumeFreezePercent, reserved2, terminalIdleTime, boardLotQuantity, tickSize, maximumGtcDays, securityEligibleIndicators, disclosedQuantityPercentAllowed, reserved6 }, bytes)

@[simp] theorem encode_length (message : SystemInformationMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SecurityEligibleIndicators.encode_length]

theorem encode_length_pos (message : SystemInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemInformationMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SecurityEligibleIndicators.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SystemInformationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SystemInformationMessage

/-- Trade Inquiry Out Message: 170 bytes -/
structure TradeInquiryOutMessage where
  secInfo : SecInfo
  fillNumber : BitVec 32
  fillQty : BitVec 32
  fillPrice : BitVec 32
  marketType : BitVec 16
  newVolume : BitVec 32
  reserved24 : Alpha 24
  buyBrokerId : Alpha 5
  sellBrokerId : Alpha 5
  traderId : BitVec 32
  requestedBy : BitVec 16
  buyAccountNumber : Alpha 10
  sellAccountNumber : Alpha 10
  buyPan : Alpha 10
  sellPan : Alpha 10
  reserved60 : Alpha 60
  deriving DecidableEq, Repr

namespace TradeInquiryOutMessage

def encode (message : TradeInquiryOutMessage) : List UInt8 :=
  SecInfo.encode message.secInfo
    ++ (encodeUInt 4 message.fillNumber
    ++ (encodeUInt 4 message.fillQty
    ++ (encodeUInt 4 message.fillPrice
    ++ (encodeUInt 2 message.marketType
    ++ (encodeUInt 4 message.newVolume
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.buyBrokerId
    ++ (Alpha.encode message.sellBrokerId
    ++ (encodeUInt 4 message.traderId
    ++ (encodeUInt 2 message.requestedBy
    ++ (Alpha.encode message.buyAccountNumber
    ++ (Alpha.encode message.sellAccountNumber
    ++ (Alpha.encode message.buyPan
    ++ (Alpha.encode message.sellPan
    ++ (Alpha.encode message.reserved60)))))))))))))))

def decode (bytes : List UInt8) : Option (TradeInquiryOutMessage × List UInt8) := do
  let (secInfo, bytes) ← SecInfo.decode bytes
  let (fillNumber, bytes) ← decodeUInt 4 bytes
  let (fillQty, bytes) ← decodeUInt 4 bytes
  let (fillPrice, bytes) ← decodeUInt 4 bytes
  let (marketType, bytes) ← decodeUInt 2 bytes
  let (newVolume, bytes) ← decodeUInt 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (buyBrokerId, bytes) ← Alpha.decode 5 bytes
  let (sellBrokerId, bytes) ← Alpha.decode 5 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (requestedBy, bytes) ← decodeUInt 2 bytes
  let (buyAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (sellAccountNumber, bytes) ← Alpha.decode 10 bytes
  let (buyPan, bytes) ← Alpha.decode 10 bytes
  let (sellPan, bytes) ← Alpha.decode 10 bytes
  let (reserved60, bytes) ← Alpha.decode 60 bytes
  pure ({ secInfo, fillNumber, fillQty, fillPrice, marketType, newVolume, reserved24, buyBrokerId, sellBrokerId, traderId, requestedBy, buyAccountNumber, sellAccountNumber, buyPan, sellPan, reserved60 }, bytes)

@[simp] theorem encode_length (message : TradeInquiryOutMessage) : (encode message).length = 170 := by
  unfold encode
  simp only [List.length_append, SecInfo.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeInquiryOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeInquiryOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SecInfo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeInquiryOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeInquiryOutMessage

/-- Update Local Database Header Message: 2 bytes -/
structure UpdateLocalDatabaseHeaderMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseHeaderMessage

def encode (message : UpdateLocalDatabaseHeaderMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseHeaderMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseHeaderMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseHeaderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseHeaderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UpdateLocalDatabaseHeaderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UpdateLocalDatabaseHeaderMessage

/-- Update Local Database Trailer Message: 2 bytes -/
structure UpdateLocalDatabaseTrailerMessage where
  reserved2 : Alpha 2
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseTrailerMessage

def encode (message : UpdateLocalDatabaseTrailerMessage) : List UInt8 :=
  Alpha.encode message.reserved2

def decode (bytes : List UInt8) : Option (UpdateLocalDatabaseTrailerMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  pure ({ reserved2 }, bytes)

@[simp] theorem encode_length (message : UpdateLocalDatabaseTrailerMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : UpdateLocalDatabaseTrailerMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UpdateLocalDatabaseTrailerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UpdateLocalDatabaseTrailerMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UpdateLocalDatabaseTrailerMessage

/-- User Unlock Approval Rejection Message: 4 bytes -/
structure UserUnlockApprovalRejectionMessage where
  userId : BitVec 32
  deriving DecidableEq, Repr

namespace UserUnlockApprovalRejectionMessage

def encode (message : UserUnlockApprovalRejectionMessage) : List UInt8 :=
  encodeUInt 4 message.userId

def decode (bytes : List UInt8) : Option (UserUnlockApprovalRejectionMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  pure ({ userId }, bytes)

@[simp] theorem encode_length (message : UserUnlockApprovalRejectionMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : UserUnlockApprovalRejectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserUnlockApprovalRejectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserUnlockApprovalRejectionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserUnlockApprovalRejectionMessage

/-- User Unlock Requested Response Message: 4 bytes -/
structure UserUnlockRequestedResponseMessage where
  userId : BitVec 32
  deriving DecidableEq, Repr

namespace UserUnlockRequestedResponseMessage

def encode (message : UserUnlockRequestedResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId

def decode (bytes : List UInt8) : Option (UserUnlockRequestedResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  pure ({ userId }, bytes)

@[simp] theorem encode_length (message : UserUnlockRequestedResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : UserUnlockRequestedResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserUnlockRequestedResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserUnlockRequestedResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserUnlockRequestedResponseMessage

/-- User Limits: 64 bytes -/
structure UserLimits where
  reserved16 : Alpha 16
  userOrderBuyValueLimit : Alpha 8
  reserved24 : Alpha 24
  userOrderSellValueLimit : Alpha 8
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace UserLimits

def encode (message : UserLimits) : List UInt8 :=
  Alpha.encode message.reserved16
    ++ (Alpha.encode message.userOrderBuyValueLimit
    ++ (Alpha.encode message.reserved24
    ++ (Alpha.encode message.userOrderSellValueLimit
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (UserLimits × List UInt8) := do
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (userOrderBuyValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  let (userOrderSellValueLimit, bytes) ← Alpha.decode 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ reserved16, userOrderBuyValueLimit, reserved24, userOrderSellValueLimit, reserved8 }, bytes)

@[simp] theorem encode_length (message : UserLimits) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UserLimits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLimits) (rest : List UInt8) :
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

end UserLimits

/-- User Order Value Limit Update Out Message: 102 bytes -/
structure UserOrderValueLimitUpdateOutMessage where
  brokerId : Alpha 5
  reserved1 : Alpha 1
  branch : BitVec 16
  reserved26 : Alpha 26
  userId : BitVec 32
  userLimits : UserLimits
  deriving DecidableEq, Repr

namespace UserOrderValueLimitUpdateOutMessage

def encode (message : UserOrderValueLimitUpdateOutMessage) : List UInt8 :=
  Alpha.encode message.brokerId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUInt 2 message.branch
    ++ (Alpha.encode message.reserved26
    ++ (encodeUInt 4 message.userId
    ++ (UserLimits.encode message.userLimits)))))

def decode (bytes : List UInt8) : Option (UserOrderValueLimitUpdateOutMessage × List UInt8) := do
  let (brokerId, bytes) ← Alpha.decode 5 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (branch, bytes) ← decodeUInt 2 bytes
  let (reserved26, bytes) ← Alpha.decode 26 bytes
  let (userId, bytes) ← decodeUInt 4 bytes
  let (userLimits, bytes) ← UserLimits.decode bytes
  pure ({ brokerId, reserved1, branch, reserved26, userId, userLimits }, bytes)

@[simp] theorem encode_length (message : UserOrderValueLimitUpdateOutMessage) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, UserLimits.encode_length]

theorem encode_length_pos (message : UserOrderValueLimitUpdateOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserOrderValueLimitUpdateOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [UserLimits.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserOrderValueLimitUpdateOutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserOrderValueLimitUpdateOutMessage

/-- Trade Modification Cancellation Status Response Message: 6 bytes -/
structure TradeModificationCancellationStatusResponseMessage where
  userId : BitVec 32
  trdModCxlBit : Alpha 1
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace TradeModificationCancellationStatusResponseMessage

def encode (message : TradeModificationCancellationStatusResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userId
    ++ (Alpha.encode message.trdModCxlBit
    ++ (Alpha.encode message.reserved1))

def decode (bytes : List UInt8) : Option (TradeModificationCancellationStatusResponseMessage × List UInt8) := do
  let (userId, bytes) ← decodeUInt 4 bytes
  let (trdModCxlBit, bytes) ← Alpha.decode 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ userId, trdModCxlBit, reserved1 }, bytes)

@[simp] theorem encode_length (message : TradeModificationCancellationStatusResponseMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeModificationCancellationStatusResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeModificationCancellationStatusResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeModificationCancellationStatusResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeModificationCancellationStatusResponseMessage

/-- Sign Off Confirmation Message: 0 bytes -/
structure SignOffConfirmationMessage where
  deriving DecidableEq, Repr

namespace SignOffConfirmationMessage

def encode (_ : SignOffConfirmationMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SignOffConfirmationMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SignOffConfirmationMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SignOffConfirmationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SignOffConfirmationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SignOffConfirmationMessage

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HeaderRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MessageRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TrailerRecordMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TrailerRecordMessage

/-- Secure Box Registration Response Message: 0 bytes -/
structure SecureBoxRegistrationResponseMessage where
  deriving DecidableEq, Repr

namespace SecureBoxRegistrationResponseMessage

def encode (_ : SecureBoxRegistrationResponseMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SecureBoxRegistrationResponseMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SecureBoxRegistrationResponseMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SecureBoxRegistrationResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SecureBoxRegistrationResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SecureBoxRegistrationResponseMessage

/-- Inner Header: 40 bytes -/
structure InnerHeader where
  innerTraderId : BitVec 32
  innerLogTime : BitVec 32
  innerAlphaChar : Alpha 2
  innerTransactionCode : BitVec 16
  innerErrorCode : BitVec 16
  innerTimestamp : BitVec 64
  innerTimeStamp1 : Alpha 8
  innerTimeStamp2 : Alpha 8
  innerMessageLength : BitVec 16
  deriving DecidableEq, Repr

namespace InnerHeader

def encode (message : InnerHeader) : List UInt8 :=
  encodeUInt 4 message.innerTraderId
    ++ (encodeUInt 4 message.innerLogTime
    ++ (Alpha.encode message.innerAlphaChar
    ++ (encodeUInt 2 message.innerTransactionCode
    ++ (encodeUInt 2 message.innerErrorCode
    ++ (encodeUInt 8 message.innerTimestamp
    ++ (Alpha.encode message.innerTimeStamp1
    ++ (Alpha.encode message.innerTimeStamp2
    ++ (encodeUInt 2 message.innerMessageLength))))))))

def decode (bytes : List UInt8) : Option (InnerHeader × List UInt8) := do
  let (innerTraderId, bytes) ← decodeUInt 4 bytes
  let (innerLogTime, bytes) ← decodeUInt 4 bytes
  let (innerAlphaChar, bytes) ← Alpha.decode 2 bytes
  let (innerTransactionCode, bytes) ← decodeUInt 2 bytes
  let (innerErrorCode, bytes) ← decodeUInt 2 bytes
  let (innerTimestamp, bytes) ← decodeUInt 8 bytes
  let (innerTimeStamp1, bytes) ← Alpha.decode 8 bytes
  let (innerTimeStamp2, bytes) ← Alpha.decode 8 bytes
  let (innerMessageLength, bytes) ← decodeUInt 2 bytes
  pure ({ innerTraderId, innerLogTime, innerAlphaChar, innerTransactionCode, innerErrorCode, innerTimestamp, innerTimeStamp1, innerTimeStamp2, innerMessageLength }, bytes)

@[simp] theorem encode_length (message : InnerHeader) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InnerHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InnerHeader) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InnerHeader

/-- Local Database Data -/
structure LocalDatabaseData where
  dataPayload : List UInt8
  deriving DecidableEq, Repr

namespace LocalDatabaseData

def encode (message : LocalDatabaseData) : List UInt8 :=
  encodeMany Byte.encode message.dataPayload

def decode (bytes : List UInt8) : Option LocalDatabaseData := do
  let dataPayload ← decodeAll Byte.decode bytes.length bytes
  pure { dataPayload }

theorem decode_encode (message : LocalDatabaseData) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.dataPayload _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.dataPayload), some_bind]
  rfl

end LocalDatabaseData

/-- Update Local Database Data Message -/
structure UpdateLocalDatabaseDataMessage where
  innerHeader : InnerHeader
  localDatabaseData : LocalDatabaseData
  deriving DecidableEq, Repr

namespace UpdateLocalDatabaseDataMessage

def encode (message : UpdateLocalDatabaseDataMessage) : List UInt8 :=
  InnerHeader.encode message.innerHeader
    ++ (LocalDatabaseData.encode message.localDatabaseData)

def decode (bytes : List UInt8) : Option UpdateLocalDatabaseDataMessage := do
  let (innerHeader, bytes) ← InnerHeader.decode bytes
  let localDatabaseData ← LocalDatabaseData.decode bytes
  pure { innerHeader, localDatabaseData }

theorem encode_length_pos (message : UpdateLocalDatabaseDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [InnerHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UpdateLocalDatabaseDataMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [InnerHeader.decode_encode, some_bind]
  dsimp only
  rw [LocalDatabaseData.decode_encode, some_bind]
  rfl

end UpdateLocalDatabaseDataMessage

/-- Any Server Message Payload, selected by Transaction Code -/
inductive ServerMessagePayload where
  | auctionInquiryResponseMessage (message : AuctionInquiryResponseMessage) -- 18017
  | branchOrderValueLimitUpdateOutMessage (message : BranchOrderValueLimitUpdateOutMessage) -- 5717
  | cancelOnLogoutStatusResponseMessage (message : CancelOnLogoutStatusResponseMessage) -- 5791
  | errorResponseMessage (message : ErrorResponseMessage) -- 2302
  | boxSignOnResponseMessage (message : BoxSignOnResponseMessage) -- 23001
  | gatewayRouterResponseMessage (message : GatewayRouterResponseMessage) -- 2401
  | controlMessageToTraderMessage (message : ControlMessageToTraderMessage) -- 5295
  | tradeConfirmationMessage (message : TradeConfirmationMessage) -- 2212
  | tradeConfirmationMessage2222 (message : TradeConfirmationMessage) -- 2222
  | tradeConfirmationMessage2282 (message : TradeConfirmationMessage) -- 2282
  | tradeConfirmationMessage2286 (message : TradeConfirmationMessage) -- 2286
  | tradeConfirmationMessage2287 (message : TradeConfirmationMessage) -- 2287
  | orderEntryOutMessage (message : OrderEntryOutMessage) -- 2012
  | orderEntryOutMessage2042 (message : OrderEntryOutMessage) -- 2042
  | orderEntryOutMessage2061 (message : OrderEntryOutMessage) -- 2061
  | orderEntryOutMessage2072 (message : OrderEntryOutMessage) -- 2072
  | orderEntryOutMessage2073 (message : OrderEntryOutMessage) -- 2073
  | orderEntryOutMessage2074 (message : OrderEntryOutMessage) -- 2074
  | orderEntryOutMessage2075 (message : OrderEntryOutMessage) -- 2075
  | orderEntryOutMessage2170 (message : OrderEntryOutMessage) -- 2170
  | orderEntryOutMessage2231 (message : OrderEntryOutMessage) -- 2231
  | orderEntryOutMessage9002 (message : OrderEntryOutMessage) -- 9002
  | orderEntryShortMessage (message : OrderEntryShortMessage) -- 2001
  | orderEntryShortMessage2071 (message : OrderEntryShortMessage) -- 2071
  | orderLimitUpdateOutMessage (message : OrderLimitUpdateOutMessage) -- 5722
  | passwordResetOutMessage (message : PasswordResetOutMessage) -- 5739
  | securityStatusChangeMessage (message : SecurityStatusChangeMessage) -- 18130
  | securityStatusChangeMessage18707 (message : SecurityStatusChangeMessage) -- 18707
  | securityMasterChangeMessage (message : SecurityMasterChangeMessage) -- 18720
  | signOnRequestOutMessage (message : SignOnRequestOutMessage) -- 5724
  | signOnResponseMessage (message : SignOnResponseMessage) -- 2301
  | systemInformationMessage (message : SystemInformationMessage) -- 1601
  | systemInformationMessage7321 (message : SystemInformationMessage) -- 7321
  | tradeInquiryOutMessage (message : TradeInquiryOutMessage) -- 2223
  | tradeInquiryOutMessage5441 (message : TradeInquiryOutMessage) -- 5441
  | updateLocalDatabaseHeaderMessage (message : UpdateLocalDatabaseHeaderMessage) -- 7307
  | updateLocalDatabaseTrailerMessage (message : UpdateLocalDatabaseTrailerMessage) -- 7308
  | userUnlockApprovalRejectionMessage (message : UserUnlockApprovalRejectionMessage) -- 5575
  | userUnlockApprovalRejectionMessage5579 (message : UserUnlockApprovalRejectionMessage) -- 5579
  | userUnlockRequestedResponseMessage (message : UserUnlockRequestedResponseMessage) -- 5425
  | userOrderValueLimitUpdateOutMessage (message : UserOrderValueLimitUpdateOutMessage) -- 5720
  | tradeModificationCancellationStatusResponseMessage (message : TradeModificationCancellationStatusResponseMessage) -- 5793
  | signOffConfirmationMessage (message : SignOffConfirmationMessage) -- 2321
  | headerRecordMessage (message : HeaderRecordMessage) -- 7011
  | messageRecordMessage (message : MessageRecordMessage) -- 7021
  | trailerRecordMessage (message : TrailerRecordMessage) -- 7031
  | secureBoxRegistrationResponseMessage (message : SecureBoxRegistrationResponseMessage) -- 23009
  | updateLocalDatabaseDataMessage (message : UpdateLocalDatabaseDataMessage) -- 7304
  deriving DecidableEq, Repr

namespace ServerMessagePayload

/-- The Transaction Code each message is sent under -/
def tag : ServerMessagePayload → BitVec 16
  | .auctionInquiryResponseMessage _ => 18017
  | .branchOrderValueLimitUpdateOutMessage _ => 5717
  | .cancelOnLogoutStatusResponseMessage _ => 5791
  | .errorResponseMessage _ => 2302
  | .boxSignOnResponseMessage _ => 23001
  | .gatewayRouterResponseMessage _ => 2401
  | .controlMessageToTraderMessage _ => 5295
  | .tradeConfirmationMessage _ => 2212
  | .tradeConfirmationMessage2222 _ => 2222
  | .tradeConfirmationMessage2282 _ => 2282
  | .tradeConfirmationMessage2286 _ => 2286
  | .tradeConfirmationMessage2287 _ => 2287
  | .orderEntryOutMessage _ => 2012
  | .orderEntryOutMessage2042 _ => 2042
  | .orderEntryOutMessage2061 _ => 2061
  | .orderEntryOutMessage2072 _ => 2072
  | .orderEntryOutMessage2073 _ => 2073
  | .orderEntryOutMessage2074 _ => 2074
  | .orderEntryOutMessage2075 _ => 2075
  | .orderEntryOutMessage2170 _ => 2170
  | .orderEntryOutMessage2231 _ => 2231
  | .orderEntryOutMessage9002 _ => 9002
  | .orderEntryShortMessage _ => 2001
  | .orderEntryShortMessage2071 _ => 2071
  | .orderLimitUpdateOutMessage _ => 5722
  | .passwordResetOutMessage _ => 5739
  | .securityStatusChangeMessage _ => 18130
  | .securityStatusChangeMessage18707 _ => 18707
  | .securityMasterChangeMessage _ => 18720
  | .signOnRequestOutMessage _ => 5724
  | .signOnResponseMessage _ => 2301
  | .systemInformationMessage _ => 1601
  | .systemInformationMessage7321 _ => 7321
  | .tradeInquiryOutMessage _ => 2223
  | .tradeInquiryOutMessage5441 _ => 5441
  | .updateLocalDatabaseHeaderMessage _ => 7307
  | .updateLocalDatabaseTrailerMessage _ => 7308
  | .userUnlockApprovalRejectionMessage _ => 5575
  | .userUnlockApprovalRejectionMessage5579 _ => 5579
  | .userUnlockRequestedResponseMessage _ => 5425
  | .userOrderValueLimitUpdateOutMessage _ => 5720
  | .tradeModificationCancellationStatusResponseMessage _ => 5793
  | .signOffConfirmationMessage _ => 2321
  | .headerRecordMessage _ => 7011
  | .messageRecordMessage _ => 7021
  | .trailerRecordMessage _ => 7031
  | .secureBoxRegistrationResponseMessage _ => 23009
  | .updateLocalDatabaseDataMessage _ => 7304

def encode : ServerMessagePayload → List UInt8
  | .auctionInquiryResponseMessage message => AuctionInquiryResponseMessage.encode message
  | .branchOrderValueLimitUpdateOutMessage message => BranchOrderValueLimitUpdateOutMessage.encode message
  | .cancelOnLogoutStatusResponseMessage message => CancelOnLogoutStatusResponseMessage.encode message
  | .errorResponseMessage message => ErrorResponseMessage.encode message
  | .boxSignOnResponseMessage message => BoxSignOnResponseMessage.encode message
  | .gatewayRouterResponseMessage message => GatewayRouterResponseMessage.encode message
  | .controlMessageToTraderMessage message => ControlMessageToTraderMessage.encode message
  | .tradeConfirmationMessage message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2222 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2282 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2286 message => TradeConfirmationMessage.encode message
  | .tradeConfirmationMessage2287 message => TradeConfirmationMessage.encode message
  | .orderEntryOutMessage message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2042 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2061 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2072 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2073 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2074 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2075 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2170 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage2231 message => OrderEntryOutMessage.encode message
  | .orderEntryOutMessage9002 message => OrderEntryOutMessage.encode message
  | .orderEntryShortMessage message => OrderEntryShortMessage.encode message
  | .orderEntryShortMessage2071 message => OrderEntryShortMessage.encode message
  | .orderLimitUpdateOutMessage message => OrderLimitUpdateOutMessage.encode message
  | .passwordResetOutMessage message => PasswordResetOutMessage.encode message
  | .securityStatusChangeMessage message => SecurityStatusChangeMessage.encode message
  | .securityStatusChangeMessage18707 message => SecurityStatusChangeMessage.encode message
  | .securityMasterChangeMessage message => SecurityMasterChangeMessage.encode message
  | .signOnRequestOutMessage message => SignOnRequestOutMessage.encode message
  | .signOnResponseMessage message => SignOnResponseMessage.encode message
  | .systemInformationMessage message => SystemInformationMessage.encode message
  | .systemInformationMessage7321 message => SystemInformationMessage.encode message
  | .tradeInquiryOutMessage message => TradeInquiryOutMessage.encode message
  | .tradeInquiryOutMessage5441 message => TradeInquiryOutMessage.encode message
  | .updateLocalDatabaseHeaderMessage message => UpdateLocalDatabaseHeaderMessage.encode message
  | .updateLocalDatabaseTrailerMessage message => UpdateLocalDatabaseTrailerMessage.encode message
  | .userUnlockApprovalRejectionMessage message => UserUnlockApprovalRejectionMessage.encode message
  | .userUnlockApprovalRejectionMessage5579 message => UserUnlockApprovalRejectionMessage.encode message
  | .userUnlockRequestedResponseMessage message => UserUnlockRequestedResponseMessage.encode message
  | .userOrderValueLimitUpdateOutMessage message => UserOrderValueLimitUpdateOutMessage.encode message
  | .tradeModificationCancellationStatusResponseMessage message => TradeModificationCancellationStatusResponseMessage.encode message
  | .signOffConfirmationMessage message => SignOffConfirmationMessage.encode message
  | .headerRecordMessage message => HeaderRecordMessage.encode message
  | .messageRecordMessage message => MessageRecordMessage.encode message
  | .trailerRecordMessage message => TrailerRecordMessage.encode message
  | .secureBoxRegistrationResponseMessage message => SecureBoxRegistrationResponseMessage.encode message
  | .updateLocalDatabaseDataMessage message => UpdateLocalDatabaseDataMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerMessagePayload :=
  if tag = 18017 then (AuctionInquiryResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.auctionInquiryResponseMessage message) else none
  else if tag = 5717 then (BranchOrderValueLimitUpdateOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.branchOrderValueLimitUpdateOutMessage message) else none
  else if tag = 5791 then (CancelOnLogoutStatusResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelOnLogoutStatusResponseMessage message) else none
  else if tag = 2302 then (ErrorResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.errorResponseMessage message) else none
  else if tag = 23001 then (BoxSignOnResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.boxSignOnResponseMessage message) else none
  else if tag = 2401 then (GatewayRouterResponseMessage.decode bytes).map fun message => .gatewayRouterResponseMessage message
  else if tag = 5295 then (ControlMessageToTraderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.controlMessageToTraderMessage message) else none
  else if tag = 2212 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage message) else none
  else if tag = 2222 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2222 message) else none
  else if tag = 2282 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2282 message) else none
  else if tag = 2286 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2286 message) else none
  else if tag = 2287 then (TradeConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeConfirmationMessage2287 message) else none
  else if tag = 2012 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage message) else none
  else if tag = 2042 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2042 message) else none
  else if tag = 2061 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2061 message) else none
  else if tag = 2072 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2072 message) else none
  else if tag = 2073 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2073 message) else none
  else if tag = 2074 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2074 message) else none
  else if tag = 2075 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2075 message) else none
  else if tag = 2170 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2170 message) else none
  else if tag = 2231 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage2231 message) else none
  else if tag = 9002 then (OrderEntryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryOutMessage9002 message) else none
  else if tag = 2001 then (OrderEntryShortMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryShortMessage message) else none
  else if tag = 2071 then (OrderEntryShortMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderEntryShortMessage2071 message) else none
  else if tag = 5722 then (OrderLimitUpdateOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderLimitUpdateOutMessage message) else none
  else if tag = 5739 then (PasswordResetOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.passwordResetOutMessage message) else none
  else if tag = 18130 then (SecurityStatusChangeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.securityStatusChangeMessage message) else none
  else if tag = 18707 then (SecurityStatusChangeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.securityStatusChangeMessage18707 message) else none
  else if tag = 18720 then (SecurityMasterChangeMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.securityMasterChangeMessage message) else none
  else if tag = 5724 then (SignOnRequestOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.signOnRequestOutMessage message) else none
  else if tag = 2301 then (SignOnResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.signOnResponseMessage message) else none
  else if tag = 1601 then (SystemInformationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemInformationMessage message) else none
  else if tag = 7321 then (SystemInformationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.systemInformationMessage7321 message) else none
  else if tag = 2223 then (TradeInquiryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryOutMessage message) else none
  else if tag = 5441 then (TradeInquiryOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeInquiryOutMessage5441 message) else none
  else if tag = 7307 then (UpdateLocalDatabaseHeaderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.updateLocalDatabaseHeaderMessage message) else none
  else if tag = 7308 then (UpdateLocalDatabaseTrailerMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.updateLocalDatabaseTrailerMessage message) else none
  else if tag = 5575 then (UserUnlockApprovalRejectionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userUnlockApprovalRejectionMessage message) else none
  else if tag = 5579 then (UserUnlockApprovalRejectionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userUnlockApprovalRejectionMessage5579 message) else none
  else if tag = 5425 then (UserUnlockRequestedResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userUnlockRequestedResponseMessage message) else none
  else if tag = 5720 then (UserOrderValueLimitUpdateOutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userOrderValueLimitUpdateOutMessage message) else none
  else if tag = 5793 then (TradeModificationCancellationStatusResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeModificationCancellationStatusResponseMessage message) else none
  else if tag = 2321 then (SignOffConfirmationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.signOffConfirmationMessage message) else none
  else if tag = 7011 then (HeaderRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.headerRecordMessage message) else none
  else if tag = 7021 then (MessageRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.messageRecordMessage message) else none
  else if tag = 7031 then (TrailerRecordMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.trailerRecordMessage message) else none
  else if tag = 23009 then (SecureBoxRegistrationResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.secureBoxRegistrationResponseMessage message) else none
  else if tag = 7304 then (UpdateLocalDatabaseDataMessage.decode bytes).map fun message => .updateLocalDatabaseDataMessage message
  else none

theorem decode_encode (message : ServerMessagePayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | auctionInquiryResponseMessage message => simp [decode, encode, tag, AuctionInquiryResponseMessage.decode_encode_nil]
  | branchOrderValueLimitUpdateOutMessage message => simp [decode, encode, tag, BranchOrderValueLimitUpdateOutMessage.decode_encode_nil]
  | cancelOnLogoutStatusResponseMessage message => simp [decode, encode, tag, CancelOnLogoutStatusResponseMessage.decode_encode_nil]
  | errorResponseMessage message => simp [decode, encode, tag, ErrorResponseMessage.decode_encode_nil]
  | boxSignOnResponseMessage message => simp [decode, encode, tag, BoxSignOnResponseMessage.decode_encode_nil]
  | gatewayRouterResponseMessage message => simp [decode, encode, tag, GatewayRouterResponseMessage.decode_encode]
  | controlMessageToTraderMessage message => simp [decode, encode, tag, ControlMessageToTraderMessage.decode_encode_nil]
  | tradeConfirmationMessage message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2222 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2282 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2286 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | tradeConfirmationMessage2287 message => simp [decode, encode, tag, TradeConfirmationMessage.decode_encode_nil]
  | orderEntryOutMessage message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2042 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2061 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2072 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2073 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2074 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2075 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2170 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage2231 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryOutMessage9002 message => simp [decode, encode, tag, OrderEntryOutMessage.decode_encode_nil]
  | orderEntryShortMessage message => simp [decode, encode, tag, OrderEntryShortMessage.decode_encode_nil]
  | orderEntryShortMessage2071 message => simp [decode, encode, tag, OrderEntryShortMessage.decode_encode_nil]
  | orderLimitUpdateOutMessage message => simp [decode, encode, tag, OrderLimitUpdateOutMessage.decode_encode_nil]
  | passwordResetOutMessage message => simp [decode, encode, tag, PasswordResetOutMessage.decode_encode_nil]
  | securityStatusChangeMessage message => simp [decode, encode, tag, SecurityStatusChangeMessage.decode_encode_nil]
  | securityStatusChangeMessage18707 message => simp [decode, encode, tag, SecurityStatusChangeMessage.decode_encode_nil]
  | securityMasterChangeMessage message => simp [decode, encode, tag, SecurityMasterChangeMessage.decode_encode_nil]
  | signOnRequestOutMessage message => simp [decode, encode, tag, SignOnRequestOutMessage.decode_encode_nil]
  | signOnResponseMessage message => simp [decode, encode, tag, SignOnResponseMessage.decode_encode_nil]
  | systemInformationMessage message => simp [decode, encode, tag, SystemInformationMessage.decode_encode_nil]
  | systemInformationMessage7321 message => simp [decode, encode, tag, SystemInformationMessage.decode_encode_nil]
  | tradeInquiryOutMessage message => simp [decode, encode, tag, TradeInquiryOutMessage.decode_encode_nil]
  | tradeInquiryOutMessage5441 message => simp [decode, encode, tag, TradeInquiryOutMessage.decode_encode_nil]
  | updateLocalDatabaseHeaderMessage message => simp [decode, encode, tag, UpdateLocalDatabaseHeaderMessage.decode_encode_nil]
  | updateLocalDatabaseTrailerMessage message => simp [decode, encode, tag, UpdateLocalDatabaseTrailerMessage.decode_encode_nil]
  | userUnlockApprovalRejectionMessage message => simp [decode, encode, tag, UserUnlockApprovalRejectionMessage.decode_encode_nil]
  | userUnlockApprovalRejectionMessage5579 message => simp [decode, encode, tag, UserUnlockApprovalRejectionMessage.decode_encode_nil]
  | userUnlockRequestedResponseMessage message => simp [decode, encode, tag, UserUnlockRequestedResponseMessage.decode_encode_nil]
  | userOrderValueLimitUpdateOutMessage message => simp [decode, encode, tag, UserOrderValueLimitUpdateOutMessage.decode_encode_nil]
  | tradeModificationCancellationStatusResponseMessage message => simp [decode, encode, tag, TradeModificationCancellationStatusResponseMessage.decode_encode_nil]
  | signOffConfirmationMessage message => simp [decode, encode, tag, SignOffConfirmationMessage.decode_encode_nil]
  | headerRecordMessage message => simp [decode, encode, tag, HeaderRecordMessage.decode_encode_nil]
  | messageRecordMessage message => simp [decode, encode, tag, MessageRecordMessage.decode_encode_nil]
  | trailerRecordMessage message => simp [decode, encode, tag, TrailerRecordMessage.decode_encode_nil]
  | secureBoxRegistrationResponseMessage message => simp [decode, encode, tag, SecureBoxRegistrationResponseMessage.decode_encode_nil]
  | updateLocalDatabaseDataMessage message => simp [decode, encode, tag, UpdateLocalDatabaseDataMessage.decode_encode]

end ServerMessagePayload

/-- Server Message: the body, which the record carries with the proof it fits its frame -/
structure ServerMessageBody where
  logTime : BitVec 32
  alphaChar : Alpha 2
  traderId : BitVec 32
  errorCode : BitVec 16
  headerTimestamp : BitVec 64
  timeStamp1 : Alpha 8
  timeStamp2 : Alpha 8
  serverMessagePayload : ServerMessagePayload
  deriving DecidableEq, Repr

namespace ServerMessageBody

def encodeBody (message : ServerMessageBody) : List UInt8 :=
  ServerMessagePayload.encode message.serverMessagePayload

def decodeBody (transactionCode : BitVec 16) (logTime : BitVec 32) (alphaChar : Alpha 2) (traderId : BitVec 32) (errorCode : BitVec 16) (headerTimestamp : BitVec 64) (timeStamp1 : Alpha 8) (timeStamp2 : Alpha 8) (bytes : List UInt8) : Option ServerMessageBody := do
  let serverMessagePayload ← ServerMessagePayload.decode transactionCode bytes
  pure { logTime, alphaChar, traderId, errorCode, headerTimestamp, timeStamp1, timeStamp2, serverMessagePayload }

theorem decodeBody_encodeBody (message : ServerMessageBody) : decodeBody (ServerMessagePayload.tag message.serverMessagePayload) message.logTime message.alphaChar message.traderId message.errorCode message.headerTimestamp message.timeStamp1 message.timeStamp2 (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [ServerMessagePayload.decode_encode, some_bind]
  rfl

end ServerMessageBody

/-- Server Message: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerMessage := Fitting ServerMessageBody.encodeBody 40 65536

namespace ServerMessage

def encode (message : ServerMessage) : List UInt8 :=
  encodeUInt 2 (ServerMessagePayload.tag message.val.serverMessagePayload)
    ++ (encodeUInt 4 message.val.logTime
    ++ (Alpha.encode message.val.alphaChar
    ++ (encodeUInt 4 message.val.traderId
    ++ (encodeUInt 2 message.val.errorCode
    ++ (encodeUInt 8 message.val.headerTimestamp
    ++ (Alpha.encode message.val.timeStamp1
    ++ (Alpha.encode message.val.timeStamp2
    ++ (encodeFramed 2 40 ServerMessageBody.encodeBody message.val))))))))

def decode (bytes : List UInt8) : Option (ServerMessage × List UInt8) := do
  let (transactionCode, bytes) ← decodeUInt 2 bytes
  let (logTime, bytes) ← decodeUInt 4 bytes
  let (alphaChar, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← decodeUInt 4 bytes
  let (errorCode, bytes) ← decodeUInt 2 bytes
  let (headerTimestamp, bytes) ← decodeUInt 8 bytes
  let (timeStamp1, bytes) ← Alpha.decode 8 bytes
  let (timeStamp2, bytes) ← Alpha.decode 8 bytes
  decodeFittingAll 2 40 ServerMessageBody.encodeBody (ServerMessageBody.decodeBody transactionCode logTime alphaChar traderId errorCode headerTimestamp timeStamp1 timeStamp2) bytes

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
  exact decodeFittingAll_encodeFramed 2 40 ServerMessageBody.encodeBody (ServerMessageBody.decodeBody (ServerMessagePayload.tag message.val.serverMessagePayload) message.val.logTime message.val.alphaChar message.val.traderId message.val.errorCode message.val.headerTimestamp message.val.timeStamp1 message.val.timeStamp2) message (ServerMessageBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
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

end Omi.NseNsecmOrderentryNnfV66Server
