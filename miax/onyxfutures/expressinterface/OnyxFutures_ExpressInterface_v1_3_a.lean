import Wire

/-!
# Miami International Holdings Express Interface v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Order Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit

Note: Self Trade Protection is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Additional Order Indicators is a bit field set, proven as its 1 byte integer rather than bit
by bit

Note: Execution Order Instructions is a bit field set, proven as its 2 byte integer rather than bit
by bit

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it
reads

License: MIT No Attribution
-/

namespace Omi.MiaxOnyxfuturesExpressinterfaceFeiV13A

/-- Order Status: one byte code -/
def OrderStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x55, 0x56, 0x57, 0x59, 0x61, 0x62, 0x63, 0x64, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x5A, 0x2A]

inductive OrderStatus where
  | successful -- Successful
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | invalidOrderType -- Invalid Order Type
  | invalidCustomerOrderHandlingInstruction -- Invalid Customer Order Handling Instruction
  | invalidTimeInForceOrItsUse -- Invalid Time In Force Or Its Use
  | invalidSelfTradeProtectionLevel -- Invalid Self Trade Protection Level
  | invalidSelfTradeProtectionInstruction -- Invalid Self Trade Protection Instruction
  | invalidMpid -- Invalid Mpid
  | invalidUseSelfTradeProtectionInstruction -- Invalid Use Self Trade Protection Instruction
  | invalidSelfTradeProtectionGroup -- Invalid Self Trade Protection Group
  | invalidUseSelfTradeProtectionGroup -- Invalid Use Self Trade Protection Group
  | invalidForCurrentTradingStatus -- Invalid For Current Trading Status
  | invalidClientOrderId -- Invalid Client Order Id
  | invalidPrice -- Invalid Price
  | invalidSize -- Invalid Size
  | invalidUseMinimumQty -- Invalid Use Minimum Qty
  | invalidInstrumentId -- Invalid Instrument Id
  | invalidUseOrderType -- Invalid Use Order Type
  | invalidPurgeGroup -- Invalid Purge Group
  | invalidOrderExpiryDateOrItsUse -- Invalid Order Expiry Date Or Its Use
  | blockedByUserMassCancel -- Blocked By User Mass Cancel
  | blockedByMfpHelpDeskMassCancel -- Blocked By Mfp Help Desk Mass Cancel
  | blockedByCrm -- Blocked By Crm
  | invalidAccount -- Invalid Account
  | invalidTradingCollar -- Invalid Trading Collar
  | invalidOperatorId -- Invalid Operator Id
  | invalidOperatorLocation -- Invalid Operator Location
  | invalidCtiCode -- Invalid Cti Code
  | invalidTextMemo -- Invalid Text Memo
  | blockedByDropCopyAcodacosfEvent -- Blocked By Drop Copy Acodacosf Event
  | dailyTradingLimitBreach -- Daily Trading Limit Breach
  | tradingCollarProtection -- Trading Collar Protection
  | duplicateOrderProtection -- Duplicate Order Protection
  | orderTypeRestriction -- Order Type Restriction
  | restrictionForCurrentTradingSession -- Restriction For Current Trading Session
  | productRestriction -- Product Restriction
  | customerOrderForRegulatedAccount -- Customer Order For Regulated Account
  | firmOrderForSegregatedAccount -- Firm Order For Segregated Account
  | orderNotAllowedWhenEthClearingNotEnabled -- Order Not Allowed When Eth Clearing Not Enabled
  | noMbboForMarketOrderWithProtectionOrMarketLimitOrder -- No Mbbo For Market Order With Protection Or Market Limit Order
  | invalidDisplayRangeQty -- Invalid Display Range Qty
  | invalidMaxFloorQty -- Invalid Max Floor Qty
  | invalidUseOfReserveOrderReplenishmentTimingInstruction -- Invalid Use Of Reserve Order Replenishment Timing Instruction
  | invalidOrderTypeForReserveOrder -- Invalid Order Type For Reserve Order
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderStatus

def toByte : OrderStatus → UInt8
  | .successful => 0x20
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .invalidOrderType => 0x43
  | .invalidCustomerOrderHandlingInstruction => 0x45
  | .invalidTimeInForceOrItsUse => 0x46
  | .invalidSelfTradeProtectionLevel => 0x47
  | .invalidSelfTradeProtectionInstruction => 0x48
  | .invalidMpid => 0x49
  | .invalidUseSelfTradeProtectionInstruction => 0x4B
  | .invalidSelfTradeProtectionGroup => 0x4C
  | .invalidUseSelfTradeProtectionGroup => 0x4D
  | .invalidForCurrentTradingStatus => 0x4E
  | .invalidClientOrderId => 0x4F
  | .invalidPrice => 0x50
  | .invalidSize => 0x51
  | .invalidUseMinimumQty => 0x52
  | .invalidInstrumentId => 0x53
  | .invalidUseOrderType => 0x55
  | .invalidPurgeGroup => 0x56
  | .invalidOrderExpiryDateOrItsUse => 0x57
  | .blockedByUserMassCancel => 0x59
  | .blockedByMfpHelpDeskMassCancel => 0x61
  | .blockedByCrm => 0x62
  | .invalidAccount => 0x63
  | .invalidTradingCollar => 0x64
  | .invalidOperatorId => 0x67
  | .invalidOperatorLocation => 0x68
  | .invalidCtiCode => 0x69
  | .invalidTextMemo => 0x6A
  | .blockedByDropCopyAcodacosfEvent => 0x6B
  | .dailyTradingLimitBreach => 0x6C
  | .tradingCollarProtection => 0x6D
  | .duplicateOrderProtection => 0x6E
  | .orderTypeRestriction => 0x6F
  | .restrictionForCurrentTradingSession => 0x70
  | .productRestriction => 0x71
  | .customerOrderForRegulatedAccount => 0x72
  | .firmOrderForSegregatedAccount => 0x73
  | .orderNotAllowedWhenEthClearingNotEnabled => 0x74
  | .noMbboForMarketOrderWithProtectionOrMarketLimitOrder => 0x75
  | .invalidDisplayRangeQty => 0x76
  | .invalidMaxFloorQty => 0x77
  | .invalidUseOfReserveOrderReplenishmentTimingInstruction => 0x78
  | .invalidOrderTypeForReserveOrder => 0x79
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x43 then .invalidOrderType
  else if byte = 0x45 then .invalidCustomerOrderHandlingInstruction
  else if byte = 0x46 then .invalidTimeInForceOrItsUse
  else if byte = 0x47 then .invalidSelfTradeProtectionLevel
  else if byte = 0x48 then .invalidSelfTradeProtectionInstruction
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4B then .invalidUseSelfTradeProtectionInstruction
  else if byte = 0x4C then .invalidSelfTradeProtectionGroup
  else if byte = 0x4D then .invalidUseSelfTradeProtectionGroup
  else if byte = 0x4E then .invalidForCurrentTradingStatus
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .invalidPrice
  else if byte = 0x51 then .invalidSize
  else if byte = 0x52 then .invalidUseMinimumQty
  else if byte = 0x53 then .invalidInstrumentId
  else if byte = 0x55 then .invalidUseOrderType
  else if byte = 0x56 then .invalidPurgeGroup
  else if byte = 0x57 then .invalidOrderExpiryDateOrItsUse
  else if byte = 0x59 then .blockedByUserMassCancel
  else if byte = 0x61 then .blockedByMfpHelpDeskMassCancel
  else if byte = 0x62 then .blockedByCrm
  else if byte = 0x63 then .invalidAccount
  else if byte = 0x64 then .invalidTradingCollar
  else if byte = 0x67 then .invalidOperatorId
  else if byte = 0x68 then .invalidOperatorLocation
  else if byte = 0x69 then .invalidCtiCode
  else if byte = 0x6A then .invalidTextMemo
  else if byte = 0x6B then .blockedByDropCopyAcodacosfEvent
  else if byte = 0x6C then .dailyTradingLimitBreach
  else if byte = 0x6D then .tradingCollarProtection
  else if byte = 0x6E then .duplicateOrderProtection
  else if byte = 0x6F then .orderTypeRestriction
  else if byte = 0x70 then .restrictionForCurrentTradingSession
  else if byte = 0x71 then .productRestriction
  else if byte = 0x72 then .customerOrderForRegulatedAccount
  else if byte = 0x73 then .firmOrderForSegregatedAccount
  else if byte = 0x74 then .orderNotAllowedWhenEthClearingNotEnabled
  else if byte = 0x75 then .noMbboForMarketOrderWithProtectionOrMarketLimitOrder
  else if byte = 0x76 then .invalidDisplayRangeQty
  else if byte = 0x77 then .invalidMaxFloorQty
  else if byte = 0x78 then .invalidUseOfReserveOrderReplenishmentTimingInstruction
  else if byte = 0x79 then .invalidOrderTypeForReserveOrder
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : OrderStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | invalidOrderType => decide
  | invalidCustomerOrderHandlingInstruction => decide
  | invalidTimeInForceOrItsUse => decide
  | invalidSelfTradeProtectionLevel => decide
  | invalidSelfTradeProtectionInstruction => decide
  | invalidMpid => decide
  | invalidUseSelfTradeProtectionInstruction => decide
  | invalidSelfTradeProtectionGroup => decide
  | invalidUseSelfTradeProtectionGroup => decide
  | invalidForCurrentTradingStatus => decide
  | invalidClientOrderId => decide
  | invalidPrice => decide
  | invalidSize => decide
  | invalidUseMinimumQty => decide
  | invalidInstrumentId => decide
  | invalidUseOrderType => decide
  | invalidPurgeGroup => decide
  | invalidOrderExpiryDateOrItsUse => decide
  | blockedByUserMassCancel => decide
  | blockedByMfpHelpDeskMassCancel => decide
  | blockedByCrm => decide
  | invalidAccount => decide
  | invalidTradingCollar => decide
  | invalidOperatorId => decide
  | invalidOperatorLocation => decide
  | invalidCtiCode => decide
  | invalidTextMemo => decide
  | blockedByDropCopyAcodacosfEvent => decide
  | dailyTradingLimitBreach => decide
  | tradingCollarProtection => decide
  | duplicateOrderProtection => decide
  | orderTypeRestriction => decide
  | restrictionForCurrentTradingSession => decide
  | productRestriction => decide
  | customerOrderForRegulatedAccount => decide
  | firmOrderForSegregatedAccount => decide
  | orderNotAllowedWhenEthClearingNotEnabled => decide
  | noMbboForMarketOrderWithProtectionOrMarketLimitOrder => decide
  | invalidDisplayRangeQty => decide
  | invalidMaxFloorQty => decide
  | invalidUseOfReserveOrderReplenishmentTimingInstruction => decide
  | invalidOrderTypeForReserveOrder => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderStatus

/-- Modify Status: one byte code -/
def ModifyStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x44, 0x45, 0x46, 0x49, 0x4A, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x53, 0x54, 0x56, 0x57, 0x59, 0x61, 0x62, 0x67, 0x68, 0x6B, 0x6C, 0x6D, 0x70, 0x71, 0x72, 0x73, 0x77, 0x5A, 0x2A]

inductive ModifyStatus where
  | successful -- Successful
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | cannotFindOrderWithTargetClientOrderId -- Cannot Find Order With Target Client Order Id
  | invalidCustomerOrderHandlingInstruction -- Invalid Customer Order Handling Instruction
  | invalidForTimeInForce -- Invalid For Time In Force
  | invalidMpid -- Invalid Mpid
  | mpidDoesNotMatchTargetOrder -- Mpid Does Not Match Target Order
  | invalidSelfTradeProtectionGroup -- Invalid Self Trade Protection Group
  | invalidUseSelfTradeProtectionGroup -- Invalid Use Self Trade Protection Group
  | invalidForCurrentTradingStatus -- Invalid For Current Trading Status
  | invalidClientOrderId -- Invalid Client Order Id
  | invalidPrice -- Invalid Price
  | invalidSize -- Invalid Size
  | invalidInstrumentId -- Invalid Instrument Id
  | invalidTargetClientOrderId -- Invalid Target Client Order Id
  | invalidPurgeGroup -- Invalid Purge Group
  | invalidOrderExpiryDateOrItsUse -- Invalid Order Expiry Date Or Its Use
  | blockedByUserMassCancel -- Blocked By User Mass Cancel
  | blockedByMfpHelpDeskMassCancel -- Blocked By Mfp Help Desk Mass Cancel
  | blockedByCrm -- Blocked By Crm
  | invalidOperatorId -- Invalid Operator Id
  | invalidOperatorLocation -- Invalid Operator Location
  | blockedByDropCopyAcodacosfEvent -- Blocked By Drop Copy Acodacosf Event
  | dailyTradingLimitBreach -- Daily Trading Limit Breach
  | tradingCollarProtection -- Trading Collar Protection
  | restrictionForCurrentTradingSession -- Restriction For Current Trading Session
  | productRestriction -- Product Restriction
  | customerOrderForRegulatedAccount -- Customer Order For Regulated Account
  | firmOrderForSegregatedAccount -- Firm Order For Segregated Account
  | invalidToChangeOrUseOfMaxFloorQty -- Invalid To Change Or Use Of Max Floor Qty
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ ModifyStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ModifyStatus

def toByte : ModifyStatus → UInt8
  | .successful => 0x20
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .cannotFindOrderWithTargetClientOrderId => 0x44
  | .invalidCustomerOrderHandlingInstruction => 0x45
  | .invalidForTimeInForce => 0x46
  | .invalidMpid => 0x49
  | .mpidDoesNotMatchTargetOrder => 0x4A
  | .invalidSelfTradeProtectionGroup => 0x4C
  | .invalidUseSelfTradeProtectionGroup => 0x4D
  | .invalidForCurrentTradingStatus => 0x4E
  | .invalidClientOrderId => 0x4F
  | .invalidPrice => 0x50
  | .invalidSize => 0x51
  | .invalidInstrumentId => 0x53
  | .invalidTargetClientOrderId => 0x54
  | .invalidPurgeGroup => 0x56
  | .invalidOrderExpiryDateOrItsUse => 0x57
  | .blockedByUserMassCancel => 0x59
  | .blockedByMfpHelpDeskMassCancel => 0x61
  | .blockedByCrm => 0x62
  | .invalidOperatorId => 0x67
  | .invalidOperatorLocation => 0x68
  | .blockedByDropCopyAcodacosfEvent => 0x6B
  | .dailyTradingLimitBreach => 0x6C
  | .tradingCollarProtection => 0x6D
  | .restrictionForCurrentTradingSession => 0x70
  | .productRestriction => 0x71
  | .customerOrderForRegulatedAccount => 0x72
  | .firmOrderForSegregatedAccount => 0x73
  | .invalidToChangeOrUseOfMaxFloorQty => 0x77
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ModifyStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x44 then .cannotFindOrderWithTargetClientOrderId
  else if byte = 0x45 then .invalidCustomerOrderHandlingInstruction
  else if byte = 0x46 then .invalidForTimeInForce
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4A then .mpidDoesNotMatchTargetOrder
  else if byte = 0x4C then .invalidSelfTradeProtectionGroup
  else if byte = 0x4D then .invalidUseSelfTradeProtectionGroup
  else if byte = 0x4E then .invalidForCurrentTradingStatus
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x50 then .invalidPrice
  else if byte = 0x51 then .invalidSize
  else if byte = 0x53 then .invalidInstrumentId
  else if byte = 0x54 then .invalidTargetClientOrderId
  else if byte = 0x56 then .invalidPurgeGroup
  else if byte = 0x57 then .invalidOrderExpiryDateOrItsUse
  else if byte = 0x59 then .blockedByUserMassCancel
  else if byte = 0x61 then .blockedByMfpHelpDeskMassCancel
  else if byte = 0x62 then .blockedByCrm
  else if byte = 0x67 then .invalidOperatorId
  else if byte = 0x68 then .invalidOperatorLocation
  else if byte = 0x6B then .blockedByDropCopyAcodacosfEvent
  else if byte = 0x6C then .dailyTradingLimitBreach
  else if byte = 0x6D then .tradingCollarProtection
  else if byte = 0x70 then .restrictionForCurrentTradingSession
  else if byte = 0x71 then .productRestriction
  else if byte = 0x72 then .customerOrderForRegulatedAccount
  else if byte = 0x73 then .firmOrderForSegregatedAccount
  else if byte = 0x77 then .invalidToChangeOrUseOfMaxFloorQty
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : ModifyStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ModifyStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | cannotFindOrderWithTargetClientOrderId => decide
  | invalidCustomerOrderHandlingInstruction => decide
  | invalidForTimeInForce => decide
  | invalidMpid => decide
  | mpidDoesNotMatchTargetOrder => decide
  | invalidSelfTradeProtectionGroup => decide
  | invalidUseSelfTradeProtectionGroup => decide
  | invalidForCurrentTradingStatus => decide
  | invalidClientOrderId => decide
  | invalidPrice => decide
  | invalidSize => decide
  | invalidInstrumentId => decide
  | invalidTargetClientOrderId => decide
  | invalidPurgeGroup => decide
  | invalidOrderExpiryDateOrItsUse => decide
  | blockedByUserMassCancel => decide
  | blockedByMfpHelpDeskMassCancel => decide
  | blockedByCrm => decide
  | invalidOperatorId => decide
  | invalidOperatorLocation => decide
  | blockedByDropCopyAcodacosfEvent => decide
  | dailyTradingLimitBreach => decide
  | tradingCollarProtection => decide
  | restrictionForCurrentTradingSession => decide
  | productRestriction => decide
  | customerOrderForRegulatedAccount => decide
  | firmOrderForSegregatedAccount => decide
  | invalidToChangeOrUseOfMaxFloorQty => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ModifyStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ModifyStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ModifyStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ModifyStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ModifyStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ModifyStatus

/-- Cancel Status: one byte code -/
def CancelStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x44, 0x49, 0x4A, 0x4E, 0x4F, 0x53, 0x54, 0x65, 0x66, 0x67, 0x68, 0x5A, 0x2A]

inductive CancelStatus where
  | successful -- Successful
  | duplicateClientOrderId -- Duplicate Client Order Id
  | notInLiveOrderWindow -- Not In Live Order Window
  | cannotFindOrderWithTargetClientOrderId -- Cannot Find Order With Target Client Order Id
  | invalidMpid -- Invalid Mpid
  | mpidDoesNotMatchTargetOrder -- Mpid Does Not Match Target Order
  | invalidForCurrentTradingStatus -- Invalid For Current Trading Status
  | invalidClientOrderId -- Invalid Client Order Id
  | invalidInstrumentId -- Invalid Instrument Id
  | invalidTargetOrderId -- Invalid Target Order Id
  | invalidOrderIdOrItsUse -- Invalid Order Id Or Its Use
  | requestNotPermitted -- Request Not Permitted
  | invalidOperatorId -- Invalid Operator Id
  | invalidOperatorLocation -- Invalid Operator Location
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelStatus

def toByte : CancelStatus → UInt8
  | .successful => 0x20
  | .duplicateClientOrderId => 0x41
  | .notInLiveOrderWindow => 0x42
  | .cannotFindOrderWithTargetClientOrderId => 0x44
  | .invalidMpid => 0x49
  | .mpidDoesNotMatchTargetOrder => 0x4A
  | .invalidForCurrentTradingStatus => 0x4E
  | .invalidClientOrderId => 0x4F
  | .invalidInstrumentId => 0x53
  | .invalidTargetOrderId => 0x54
  | .invalidOrderIdOrItsUse => 0x65
  | .requestNotPermitted => 0x66
  | .invalidOperatorId => 0x67
  | .invalidOperatorLocation => 0x68
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .duplicateClientOrderId
  else if byte = 0x42 then .notInLiveOrderWindow
  else if byte = 0x44 then .cannotFindOrderWithTargetClientOrderId
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4A then .mpidDoesNotMatchTargetOrder
  else if byte = 0x4E then .invalidForCurrentTradingStatus
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x53 then .invalidInstrumentId
  else if byte = 0x54 then .invalidTargetOrderId
  else if byte = 0x65 then .invalidOrderIdOrItsUse
  else if byte = 0x66 then .requestNotPermitted
  else if byte = 0x67 then .invalidOperatorId
  else if byte = 0x68 then .invalidOperatorLocation
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : CancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | duplicateClientOrderId => decide
  | notInLiveOrderWindow => decide
  | cannotFindOrderWithTargetClientOrderId => decide
  | invalidMpid => decide
  | mpidDoesNotMatchTargetOrder => decide
  | invalidForCurrentTradingStatus => decide
  | invalidClientOrderId => decide
  | invalidInstrumentId => decide
  | invalidTargetOrderId => decide
  | invalidOrderIdOrItsUse => decide
  | requestNotPermitted => decide
  | invalidOperatorId => decide
  | invalidOperatorLocation => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelStatus

/-- Mass Cancel Status: one byte code -/
def MassCancelStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x49, 0x4F, 0x67, 0x68, 0x2A, 0x5A]

inductive MassCancelStatus where
  | successful -- Successful
  | invalidAction -- Invalid Action
  | invalidScope -- Invalid Scope
  | invalidPurgeGroup -- Invalid Purge Group
  | notInLiveOrderWindow -- Not In Live Order Window
  | invalidProductGroupCode -- Invalid Product Group Code
  | invalidProductType -- Invalid Product Type
  | invalidMpid -- Invalid Mpid
  | invalidClientOrderId -- Invalid Client Order Id
  | invalidOperatorId -- Invalid Operator Id
  | invalidOperatorLocation -- Invalid Operator Location
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | undefined -- Undefined
  | unlisted (byte : { byte : UInt8 // byte ∉ MassCancelStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassCancelStatus

def toByte : MassCancelStatus → UInt8
  | .successful => 0x20
  | .invalidAction => 0x41
  | .invalidScope => 0x42
  | .invalidPurgeGroup => 0x43
  | .notInLiveOrderWindow => 0x44
  | .invalidProductGroupCode => 0x45
  | .invalidProductType => 0x46
  | .invalidMpid => 0x49
  | .invalidClientOrderId => 0x4F
  | .invalidOperatorId => 0x67
  | .invalidOperatorLocation => 0x68
  | .downgradedFromOlderVersion => 0x2A
  | .undefined => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassCancelStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .invalidAction
  else if byte = 0x42 then .invalidScope
  else if byte = 0x43 then .invalidPurgeGroup
  else if byte = 0x44 then .notInLiveOrderWindow
  else if byte = 0x45 then .invalidProductGroupCode
  else if byte = 0x46 then .invalidProductType
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x67 then .invalidOperatorId
  else if byte = 0x68 then .invalidOperatorLocation
  else if byte = 0x2A then .downgradedFromOlderVersion
  else .undefined

def ofByte (byte : UInt8) : MassCancelStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassCancelStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | invalidAction => decide
  | invalidScope => decide
  | invalidPurgeGroup => decide
  | notInLiveOrderWindow => decide
  | invalidProductGroupCode => decide
  | invalidProductType => decide
  | invalidMpid => decide
  | invalidClientOrderId => decide
  | invalidOperatorId => decide
  | invalidOperatorLocation => decide
  | downgradedFromOlderVersion => decide
  | undefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassCancelStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassCancelStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassCancelStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : MassCancelStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : MassCancelStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassCancelStatus

/-- Strategy Creation Status: one byte code -/
def StrategyCreationStatus.codes : List UInt8 :=
  [0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4F, 0x5A, 0x67, 0x68, 0x2A]

inductive StrategyCreationStatus where
  | successful -- Successful
  | invalidNumberOfLegs -- Invalid Number Of Legs
  | invalidNotAllowedStrategy -- Invalid Not Allowed Strategy
  | invalidLegRatio -- Invalid Leg Ratio
  | reservedForFutureUse -- Reserved For Future Use
  | repeatingInstrument -- Repeating Instrument
  | noMoreStrategiesCanBeCreated -- No More Strategies Can Be Created
  | notInLiveOrderWindow -- Not In Live Order Window
  | invalidLegInstrument -- Invalid Leg Instrument
  | invalidMpid -- Invalid Mpid
  | invalidClientOrderId -- Invalid Client Order Id
  | undefined -- Undefined
  | invalidOperatorId -- Invalid Operator Id
  | invalidOperatorLocation -- Invalid Operator Location
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ StrategyCreationStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StrategyCreationStatus

def toByte : StrategyCreationStatus → UInt8
  | .successful => 0x20
  | .invalidNumberOfLegs => 0x41
  | .invalidNotAllowedStrategy => 0x42
  | .invalidLegRatio => 0x43
  | .reservedForFutureUse => 0x44
  | .repeatingInstrument => 0x45
  | .noMoreStrategiesCanBeCreated => 0x46
  | .notInLiveOrderWindow => 0x47
  | .invalidLegInstrument => 0x48
  | .invalidMpid => 0x49
  | .invalidClientOrderId => 0x4F
  | .undefined => 0x5A
  | .invalidOperatorId => 0x67
  | .invalidOperatorLocation => 0x68
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StrategyCreationStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x41 then .invalidNumberOfLegs
  else if byte = 0x42 then .invalidNotAllowedStrategy
  else if byte = 0x43 then .invalidLegRatio
  else if byte = 0x44 then .reservedForFutureUse
  else if byte = 0x45 then .repeatingInstrument
  else if byte = 0x46 then .noMoreStrategiesCanBeCreated
  else if byte = 0x47 then .notInLiveOrderWindow
  else if byte = 0x48 then .invalidLegInstrument
  else if byte = 0x49 then .invalidMpid
  else if byte = 0x4F then .invalidClientOrderId
  else if byte = 0x5A then .undefined
  else if byte = 0x67 then .invalidOperatorId
  else if byte = 0x68 then .invalidOperatorLocation
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : StrategyCreationStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StrategyCreationStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | invalidNumberOfLegs => decide
  | invalidNotAllowedStrategy => decide
  | invalidLegRatio => decide
  | reservedForFutureUse => decide
  | repeatingInstrument => decide
  | noMoreStrategiesCanBeCreated => decide
  | notInLiveOrderWindow => decide
  | invalidLegInstrument => decide
  | invalidMpid => decide
  | invalidClientOrderId => decide
  | undefined => decide
  | invalidOperatorId => decide
  | invalidOperatorLocation => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StrategyCreationStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StrategyCreationStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StrategyCreationStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StrategyCreationStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StrategyCreationStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StrategyCreationStatus

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32, 0x2A]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | downgradedForOlderVersion -- Downgraded For Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .downgradedForOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startOfTestSession
  else if byte = 0x32 then .endOfTestSession
  else .downgradedForOlderVersion

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startOfTestSession => decide
  | endOfTestSession => decide
  | downgradedForOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SystemStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x49, 0x44, 0x46, 0x43, 0x58]

inductive TimeInForce where
  | ioc -- Ioc
  | day -- Day
  | fok -- Fok
  | gtc -- Gtc
  | gtd -- Gtd
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .ioc => 0x49
  | .day => 0x44
  | .fok => 0x46
  | .gtc => 0x43
  | .gtd => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x49 then .ioc
  else if byte = 0x44 then .day
  else if byte = 0x46 then .fok
  else if byte = 0x43 then .gtc
  else .gtd

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | ioc => decide
  | day => decide
  | fok => decide
  | gtc => decide
  | gtd => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TimeInForce) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37]

inductive OrderType where
  | limitOrder -- Limit Order
  | stopLimitOrder -- Stop Limit Order
  | marketOrder -- Market Order
  | stopMarketOrder -- Stop Market Order
  | marketOrderWithProtection -- Market Order With Protection
  | marketLimitOrder -- Market Limit Order
  | stopMarketOrderWithProtection -- Stop Market Order With Protection
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .limitOrder => 0x31
  | .stopLimitOrder => 0x32
  | .marketOrder => 0x33
  | .stopMarketOrder => 0x34
  | .marketOrderWithProtection => 0x35
  | .marketLimitOrder => 0x36
  | .stopMarketOrderWithProtection => 0x37
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x31 then .limitOrder
  else if byte = 0x32 then .stopLimitOrder
  else if byte = 0x33 then .marketOrder
  else if byte = 0x34 then .stopMarketOrder
  else if byte = 0x35 then .marketOrderWithProtection
  else if byte = 0x36 then .marketLimitOrder
  else .stopMarketOrderWithProtection

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | limitOrder => decide
  | stopLimitOrder => decide
  | marketOrder => decide
  | stopMarketOrder => decide
  | marketOrderWithProtection => decide
  | marketLimitOrder => decide
  | stopMarketOrderWithProtection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OrderType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Customer Order Handling Instruction: one byte code -/
def CustomerOrderHandlingInstruction.codes : List UInt8 :=
  [0x57, 0x59, 0x43, 0x47, 0x48, 0x44]

inductive CustomerOrderHandlingInstruction where
  | desk -- Desk
  | electronic -- Electronic
  | vendorProvidedPlatformBilledByExecutingBroker -- Vendor Provided Platform Billed By Executing Broker
  | sponsoredAccessViaExchangeApiOrFixProvidedByExecutingBroker -- Sponsored Access Via Exchange Api Or Fix Provided By Executing Broker
  | premiumAlgorithmicTradingProviderBilledByExecutingBroker -- Premium Algorithmic Trading Provider Billed By Executing Broker
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerOrderHandlingInstruction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerOrderHandlingInstruction

def toByte : CustomerOrderHandlingInstruction → UInt8
  | .desk => 0x57
  | .electronic => 0x59
  | .vendorProvidedPlatformBilledByExecutingBroker => 0x43
  | .sponsoredAccessViaExchangeApiOrFixProvidedByExecutingBroker => 0x47
  | .premiumAlgorithmicTradingProviderBilledByExecutingBroker => 0x48
  | .other => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustomerOrderHandlingInstruction :=
  if byte = 0x57 then .desk
  else if byte = 0x59 then .electronic
  else if byte = 0x43 then .vendorProvidedPlatformBilledByExecutingBroker
  else if byte = 0x47 then .sponsoredAccessViaExchangeApiOrFixProvidedByExecutingBroker
  else if byte = 0x48 then .premiumAlgorithmicTradingProviderBilledByExecutingBroker
  else .other

def ofByte (byte : UInt8) : CustomerOrderHandlingInstruction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerOrderHandlingInstruction) : ofByte value.toByte = value := by
  cases value with
  | desk => decide
  | electronic => decide
  | vendorProvidedPlatformBilledByExecutingBroker => decide
  | sponsoredAccessViaExchangeApiOrFixProvidedByExecutingBroker => decide
  | premiumAlgorithmicTradingProviderBilledByExecutingBroker => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerOrderHandlingInstruction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerOrderHandlingInstruction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerOrderHandlingInstruction) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CustomerOrderHandlingInstruction) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CustomerOrderHandlingInstruction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerOrderHandlingInstruction

/-- Cti Code: one byte code -/
def CtiCode.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive CtiCode where
  | cti1 -- Cti 1
  | cti2 -- Cti 2
  | cti3 -- Cti 3
  | cti4 -- Cti 4
  | unlisted (byte : { byte : UInt8 // byte ∉ CtiCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CtiCode

def toByte : CtiCode → UInt8
  | .cti1 => 0x31
  | .cti2 => 0x32
  | .cti3 => 0x33
  | .cti4 => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CtiCode :=
  if byte = 0x31 then .cti1
  else if byte = 0x32 then .cti2
  else if byte = 0x33 then .cti3
  else .cti4

def ofByte (byte : UInt8) : CtiCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CtiCode) : ofByte value.toByte = value := by
  cases value with
  | cti1 => decide
  | cti2 => decide
  | cti3 => decide
  | cti4 => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CtiCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CtiCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CtiCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CtiCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CtiCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CtiCode

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x31, 0x32, 0x33, 0x34, 0x5A, 0x2A]

inductive CancelReason where
  | minQuantityNotSatisfiedOrFokMinQuantityNotSatisfied -- Min Quantity Not Satisfied Or Fok Min Quantity Not Satisfied
  | reservedForFutureUse -- Reserved For Future Use
  | timeInForceCanceled -- Time In Force Canceled
  | autoCancelOnDisconnectAcod -- Auto Cancel On Disconnect Acod
  | breachedDailyTradingPriceRange -- Breached Daily Trading Price Range
  | autoCancelOnSystemFailureAcosf -- Auto Cancel On System Failure Acosf
  | tradingCollarProtection -- Trading Collar Protection
  | canceledByHelpdeskOrOverMiaxMemberFirmPortal -- Canceled By Helpdesk Or Over Miax Member Firm Portal
  | gtcgtdCustomerOrderIntroductionForRegulatedAccount -- Gtcgtd Customer Order Introduction For Regulated Account
  | massCancelMpidOrProductGroupProductTypeByUser -- Mass Cancel Mpid Or Product Group Product Type By User
  | massCancelMpidOrProductGroupProductTypeByHelpdeskOrOverMiaxMemberFirmPortal -- Mass Cancel Mpid Or Product Group Product Type By Helpdesk Or Over Miax Member Firm Portal
  | massCancelSessionByUser -- Mass Cancel Session By User
  | massCancelSessionByHelpdeskOrOverMiaxMemberFirmPortal -- Mass Cancel Session By Helpdesk Or Over Miax Member Firm Portal
  | crossingStrategyMatchPriceRangeSmpr -- Crossing Strategy Match Price Range Smpr
  | crmProtection -- Crm Protection
  | dropCopyAcodacosfEvent -- Drop Copy Acodacosf Event
  | marketableOrderOutsideStrategyMatchPriceRangeSmpr -- Marketable Order Outside Strategy Match Price Range Smpr
  | gtcgtdOrderIntroductionBreachedPerOrderRiskMetrics -- Gtcgtd Order Introduction Breached Per Order Risk Metrics
  | gtcgtdFirmOrderIntroductionForSegregatedAccount -- Gtcgtd Firm Order Introduction For Segregated Account
  | orderNotAllowedWhenEthClearingNotEnabled -- Order Not Allowed When Eth Clearing Not Enabled
  | canceledByUserThroughOrderEntrySession -- Canceled By User Through Order Entry Session
  | canceledByUserThroughASessionOtherThanTheOrderEntrySession -- Canceled By User Through A Session Other Than The Order Entry Session
  | stopOrderNoLongerValid -- Stop Order No Longer Valid
  | cancelNewestInstruction -- Cancel Newest Instruction
  | cancelOldestInstruction -- Cancel Oldest Instruction
  | cancelBothInstruction -- Cancel Both Instruction
  | decrementAndCancelInstruction -- Decrement And Cancel Instruction
  | undefinedReason -- Undefined Reason
  | downgradedFromOlderVersion -- Downgraded From Older Version
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .minQuantityNotSatisfiedOrFokMinQuantityNotSatisfied => 0x41
  | .reservedForFutureUse => 0x42
  | .timeInForceCanceled => 0x43
  | .autoCancelOnDisconnectAcod => 0x44
  | .breachedDailyTradingPriceRange => 0x45
  | .autoCancelOnSystemFailureAcosf => 0x46
  | .tradingCollarProtection => 0x47
  | .canceledByHelpdeskOrOverMiaxMemberFirmPortal => 0x48
  | .gtcgtdCustomerOrderIntroductionForRegulatedAccount => 0x49
  | .massCancelMpidOrProductGroupProductTypeByUser => 0x4A
  | .massCancelMpidOrProductGroupProductTypeByHelpdeskOrOverMiaxMemberFirmPortal => 0x4B
  | .massCancelSessionByUser => 0x4C
  | .massCancelSessionByHelpdeskOrOverMiaxMemberFirmPortal => 0x4D
  | .crossingStrategyMatchPriceRangeSmpr => 0x4E
  | .crmProtection => 0x4F
  | .dropCopyAcodacosfEvent => 0x50
  | .marketableOrderOutsideStrategyMatchPriceRangeSmpr => 0x51
  | .gtcgtdOrderIntroductionBreachedPerOrderRiskMetrics => 0x52
  | .gtcgtdFirmOrderIntroductionForSegregatedAccount => 0x53
  | .orderNotAllowedWhenEthClearingNotEnabled => 0x54
  | .canceledByUserThroughOrderEntrySession => 0x55
  | .canceledByUserThroughASessionOtherThanTheOrderEntrySession => 0x56
  | .stopOrderNoLongerValid => 0x57
  | .cancelNewestInstruction => 0x31
  | .cancelOldestInstruction => 0x32
  | .cancelBothInstruction => 0x33
  | .decrementAndCancelInstruction => 0x34
  | .undefinedReason => 0x5A
  | .downgradedFromOlderVersion => 0x2A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x41 then .minQuantityNotSatisfiedOrFokMinQuantityNotSatisfied
  else if byte = 0x42 then .reservedForFutureUse
  else if byte = 0x43 then .timeInForceCanceled
  else if byte = 0x44 then .autoCancelOnDisconnectAcod
  else if byte = 0x45 then .breachedDailyTradingPriceRange
  else if byte = 0x46 then .autoCancelOnSystemFailureAcosf
  else if byte = 0x47 then .tradingCollarProtection
  else if byte = 0x48 then .canceledByHelpdeskOrOverMiaxMemberFirmPortal
  else if byte = 0x49 then .gtcgtdCustomerOrderIntroductionForRegulatedAccount
  else if byte = 0x4A then .massCancelMpidOrProductGroupProductTypeByUser
  else if byte = 0x4B then .massCancelMpidOrProductGroupProductTypeByHelpdeskOrOverMiaxMemberFirmPortal
  else if byte = 0x4C then .massCancelSessionByUser
  else if byte = 0x4D then .massCancelSessionByHelpdeskOrOverMiaxMemberFirmPortal
  else if byte = 0x4E then .crossingStrategyMatchPriceRangeSmpr
  else if byte = 0x4F then .crmProtection
  else if byte = 0x50 then .dropCopyAcodacosfEvent
  else if byte = 0x51 then .marketableOrderOutsideStrategyMatchPriceRangeSmpr
  else if byte = 0x52 then .gtcgtdOrderIntroductionBreachedPerOrderRiskMetrics
  else if byte = 0x53 then .gtcgtdFirmOrderIntroductionForSegregatedAccount
  else if byte = 0x54 then .orderNotAllowedWhenEthClearingNotEnabled
  else if byte = 0x55 then .canceledByUserThroughOrderEntrySession
  else if byte = 0x56 then .canceledByUserThroughASessionOtherThanTheOrderEntrySession
  else if byte = 0x57 then .stopOrderNoLongerValid
  else if byte = 0x31 then .cancelNewestInstruction
  else if byte = 0x32 then .cancelOldestInstruction
  else if byte = 0x33 then .cancelBothInstruction
  else if byte = 0x34 then .decrementAndCancelInstruction
  else if byte = 0x5A then .undefinedReason
  else .downgradedFromOlderVersion

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | minQuantityNotSatisfiedOrFokMinQuantityNotSatisfied => decide
  | reservedForFutureUse => decide
  | timeInForceCanceled => decide
  | autoCancelOnDisconnectAcod => decide
  | breachedDailyTradingPriceRange => decide
  | autoCancelOnSystemFailureAcosf => decide
  | tradingCollarProtection => decide
  | canceledByHelpdeskOrOverMiaxMemberFirmPortal => decide
  | gtcgtdCustomerOrderIntroductionForRegulatedAccount => decide
  | massCancelMpidOrProductGroupProductTypeByUser => decide
  | massCancelMpidOrProductGroupProductTypeByHelpdeskOrOverMiaxMemberFirmPortal => decide
  | massCancelSessionByUser => decide
  | massCancelSessionByHelpdeskOrOverMiaxMemberFirmPortal => decide
  | crossingStrategyMatchPriceRangeSmpr => decide
  | crmProtection => decide
  | dropCopyAcodacosfEvent => decide
  | marketableOrderOutsideStrategyMatchPriceRangeSmpr => decide
  | gtcgtdOrderIntroductionBreachedPerOrderRiskMetrics => decide
  | gtcgtdFirmOrderIntroductionForSegregatedAccount => decide
  | orderNotAllowedWhenEthClearingNotEnabled => decide
  | canceledByUserThroughOrderEntrySession => decide
  | canceledByUserThroughASessionOtherThanTheOrderEntrySession => decide
  | stopOrderNoLongerValid => decide
  | cancelNewestInstruction => decide
  | cancelOldestInstruction => decide
  | cancelBothInstruction => decide
  | decrementAndCancelInstruction => decide
  | undefinedReason => decide
  | downgradedFromOlderVersion => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CancelReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Update Status: one byte code -/
def UpdateStatus.codes : List UInt8 :=
  [0x53]

inductive UpdateStatus where
  | stopOrderTriggered -- Stop Order Triggered
  | unlisted (byte : { byte : UInt8 // byte ∉ UpdateStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace UpdateStatus

def toByte : UpdateStatus → UInt8
  | .stopOrderTriggered => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : UpdateStatus :=
  .stopOrderTriggered

def ofByte (byte : UInt8) : UpdateStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : UpdateStatus) : ofByte value.toByte = value := by
  cases value with
  | stopOrderTriggered => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : UpdateStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (UpdateStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : UpdateStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : UpdateStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : UpdateStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end UpdateStatus

/-- Trade Status: one byte code -/
def TradeStatus.codes : List UInt8 :=
  [0x45, 0x43, 0x58]

inductive TradeStatus where
  | newExecution -- New Execution
  | priceSizeCorrection -- Price Size Correction
  | tradeCancellation -- Trade Cancellation
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeStatus

def toByte : TradeStatus → UInt8
  | .newExecution => 0x45
  | .priceSizeCorrection => 0x43
  | .tradeCancellation => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeStatus :=
  if byte = 0x45 then .newExecution
  else if byte = 0x43 then .priceSizeCorrection
  else .tradeCancellation

def ofByte (byte : UInt8) : TradeStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeStatus) : ofByte value.toByte = value := by
  cases value with
  | newExecution => decide
  | priceSizeCorrection => decide
  | tradeCancellation => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradeStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradeStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeStatus

/-- Last Price Restatement: one byte code -/
def LastPriceRestatement.codes : List UInt8 :=
  [0x59, 0x4E]

inductive LastPriceRestatement where
  | finalTradePriceForTasbticTrade -- Final Trade Price For Tasbtic Trade
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ LastPriceRestatement.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LastPriceRestatement

def toByte : LastPriceRestatement → UInt8
  | .finalTradePriceForTasbticTrade => 0x59
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LastPriceRestatement :=
  if byte = 0x59 then .finalTradePriceForTasbticTrade
  else .notApplicable

def ofByte (byte : UInt8) : LastPriceRestatement :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LastPriceRestatement) : ofByte value.toByte = value := by
  cases value with
  | finalTradePriceForTasbticTrade => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LastPriceRestatement) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LastPriceRestatement × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LastPriceRestatement) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LastPriceRestatement) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LastPriceRestatement) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LastPriceRestatement

/-- Scope: one byte code -/
def Scope.codes : List UInt8 :=
  [0x4D, 0x50, 0x54, 0x53]

inductive Scope where
  | mpid -- Mpid
  | mpidProductGroup -- Mpid Product Group
  | mpidProductGroupProductType -- Mpid Product Group Product Type
  | session -- Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Scope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Scope

def toByte : Scope → UInt8
  | .mpid => 0x4D
  | .mpidProductGroup => 0x50
  | .mpidProductGroupProductType => 0x54
  | .session => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Scope :=
  if byte = 0x4D then .mpid
  else if byte = 0x50 then .mpidProductGroup
  else if byte = 0x54 then .mpidProductGroupProductType
  else .session

def ofByte (byte : UInt8) : Scope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Scope) : ofByte value.toByte = value := by
  cases value with
  | mpid => decide
  | mpidProductGroup => decide
  | mpidProductGroupProductType => decide
  | session => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Scope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Scope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Scope) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Scope) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Scope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Scope

/-- Action: one byte code -/
def Action.codes : List UInt8 :=
  [0x42, 0x4D, 0x58, 0x52]

inductive Action where
  | blockOnly -- Block Only
  | massCancelOnly -- Mass Cancel Only
  | blockAndMassCancel -- Block And Mass Cancel
  | removeBlockingForTheSpecifiedScope -- Remove Blocking For The Specified Scope
  | unlisted (byte : { byte : UInt8 // byte ∉ Action.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Action

def toByte : Action → UInt8
  | .blockOnly => 0x42
  | .massCancelOnly => 0x4D
  | .blockAndMassCancel => 0x58
  | .removeBlockingForTheSpecifiedScope => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Action :=
  if byte = 0x42 then .blockOnly
  else if byte = 0x4D then .massCancelOnly
  else if byte = 0x58 then .blockAndMassCancel
  else .removeBlockingForTheSpecifiedScope

def ofByte (byte : UInt8) : Action :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Action) : ofByte value.toByte = value := by
  cases value with
  | blockOnly => decide
  | massCancelOnly => decide
  | blockAndMassCancel => decide
  | removeBlockingForTheSpecifiedScope => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Action) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Action × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Action) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Action) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Action) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Action

/-- Product Type: one byte code -/
def ProductType.codes : List UInt8 :=
  [0x4F, 0x53, 0x45, 0x42, 0x43]

inductive ProductType where
  | outrightFutures -- Outright Futures
  | standardCalendarSpread -- Standard Calendar Spread
  | equityCalendarSpread -- Equity Calendar Spread
  | butterflySpread -- Butterfly Spread
  | crossProductSpread -- Cross Product Spread
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductType

def toByte : ProductType → UInt8
  | .outrightFutures => 0x4F
  | .standardCalendarSpread => 0x53
  | .equityCalendarSpread => 0x45
  | .butterflySpread => 0x42
  | .crossProductSpread => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductType :=
  if byte = 0x4F then .outrightFutures
  else if byte = 0x53 then .standardCalendarSpread
  else if byte = 0x45 then .equityCalendarSpread
  else if byte = 0x42 then .butterflySpread
  else .crossProductSpread

def ofByte (byte : UInt8) : ProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductType) : ofByte value.toByte = value := by
  cases value with
  | outrightFutures => decide
  | standardCalendarSpread => decide
  | equityCalendarSpread => decide
  | butterflySpread => decide
  | crossProductSpread => decide
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

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x58, 0x53, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | successful -- Successful
  | rejected -- Rejected
  | requestedSessionIsNotAvailable -- Requested Session Is Not Available
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .successful => 0x20
  | .rejected => 0x58
  | .requestedSessionIsNotAvailable => 0x53
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x58 then .rejected
  else if byte = 0x53 then .requestedSessionIsNotAvailable
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | rejected => decide
  | requestedSessionIsNotAvailable => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LoginStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badPacket -- Bad Packet
  | timedOut -- Timed Out
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badPacket => 0x42
  | .timedOut => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badPacket
  else if byte = 0x4C then .timedOut
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badPacket => decide
  | timedOut => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : LogoutReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- New Order Response Message: 56 bytes -/
structure NewOrderResponseMessage where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  instrumentId : BitVec 32
  orderId : BitVec 64
  orderStatus : OrderStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace NewOrderResponseMessage

def encode (message : NewOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (OrderStatus.encode message.orderStatus
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderStatus, bytes) ← OrderStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, instrumentId, orderId, orderStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : NewOrderResponseMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderStatus.encode_length]

theorem encode_length_pos (message : NewOrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderResponseMessage

/-- Modify Order Response: 80 bytes -/
structure ModifyOrderResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentId : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  modifyStatus : ModifyStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (ModifyStatus.encode message.modifyStatus
    ++ (Alpha.encode message.reserved10))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (modifyStatus, bytes) ← ModifyStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, originalClientOrderId, instrumentId, orderId, leavesQty, modifyStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ModifyStatus.encode_length]

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ModifyStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderResponse

/-- Cancel Order Response: 76 bytes -/
structure CancelOrderResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentId : BitVec 32
  orderId : BitVec 64
  cancelStatus : CancelStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderResponse

def encode (message : CancelOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (CancelStatus.encode message.cancelStatus
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (CancelOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (cancelStatus, bytes) ← CancelStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, originalClientOrderId, instrumentId, orderId, cancelStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderResponse) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CancelStatus.encode_length]

theorem encode_length_pos (message : CancelOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CancelStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderResponse

/-- Mass Cancel Response: 44 bytes -/
structure MassCancelResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  massCancelStatus : MassCancelStatus
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace MassCancelResponse

def encode (message : MassCancelResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (MassCancelStatus.encode message.massCancelStatus
    ++ (Alpha.encode message.reserved10))))

def decode (bytes : List UInt8) : Option (MassCancelResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (massCancelStatus, bytes) ← MassCancelStatus.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, massCancelStatus, reserved10 }, bytes)

@[simp] theorem encode_length (message : MassCancelResponse) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MassCancelStatus.encode_length]

theorem encode_length_pos (message : MassCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MassCancelStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelResponse

/-- Strategy Creation Response Message: 54 bytes -/
structure StrategyCreationResponseMessage where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  instrumentId : BitVec 32
  strategyCreationStatus : StrategyCreationStatus
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace StrategyCreationResponseMessage

def encode (message : StrategyCreationResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (StrategyCreationStatus.encode message.strategyCreationStatus
    ++ (Alpha.encode message.reserved16)))))

def decode (bytes : List UInt8) : Option (StrategyCreationResponseMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (strategyCreationStatus, bytes) ← StrategyCreationStatus.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, instrumentId, strategyCreationStatus, reserved16 }, bytes)

@[simp] theorem encode_length (message : StrategyCreationResponseMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, StrategyCreationStatus.encode_length]

theorem encode_length_pos (message : StrategyCreationResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyCreationResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, StrategyCreationStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyCreationResponseMessage

/-- System State Notification Message: 26 bytes -/
structure SystemStateNotificationMessage where
  matchingEngineTime : BitVec 64
  version : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SystemStateNotificationMessage

def encode (message : SystemStateNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.version
    ++ (encodeUInt 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (SystemStateNotificationMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (version, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, version, sessionId, systemStatus, reserved8 }, bytes)

@[simp] theorem encode_length (message : SystemStateNotificationMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SystemStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemStateNotificationMessage

/-- New Order Notification: 190 bytes -/
structure NewOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  orderId : BitVec 64
  clientSendTime : BitVec 64
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  account : Alpha 16
  clientOrderId : Alpha 20
  instrumentId : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  size : BitVec 32
  orderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : OrderType
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : CustomerOrderHandlingInstruction
  additionalOrderIndicators : BitVec 8
  minQty : BitVec 32
  orderExpiryDate : BitVec 16
  tradingCollarDollarValue : BitVec 64
  ctiCode : CtiCode
  textMemo : Alpha 20
  maxFloorQty : BitVec 32
  displayRangeQty : BitVec 32
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace NewOrderNotification

def encode (message : NewOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (CustomerOrderHandlingInstruction.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (CtiCode.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (encodeUIntLE 4 message.displayRangeQty
    ++ (Alpha.encode message.reserved24)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← CustomerOrderHandlingInstruction.decode bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (ctiCode, bytes) ← CtiCode.decode bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (displayRangeQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ matchingEngineTime, mpId, orderId, clientSendTime, operatorId, operatorLocation, account, clientOrderId, instrumentId, price, stopOrderTriggerPrice, size, orderInstructions, timeInForce, orderType, selfTradeProtection, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, minQty, orderExpiryDate, tradingCollarDollarValue, ctiCode, textMemo, maxFloorQty, displayRangeQty, reserved24 }, bytes)

@[simp] theorem encode_length (message : NewOrderNotification) : (encode message).length = 190 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TimeInForce.encode_length, OrderType.encode_length, CustomerOrderHandlingInstruction.encode_length, CtiCode.encode_length]

theorem encode_length_pos (message : NewOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerOrderHandlingInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CtiCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderNotification

/-- Modify Order Notification: 160 bytes -/
structure ModifyOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  orderId : BitVec 64
  clientSendTime : BitVec 64
  leavesQty : BitVec 32
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentId : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  size : BitVec 32
  orderExpiryDate : BitVec 16
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : CustomerOrderHandlingInstruction
  additionalOrderIndicators : BitVec 8
  maxFloorQty : BitVec 32
  reserved28 : Alpha 28
  deriving DecidableEq, Repr

namespace ModifyOrderNotification

def encode (message : ModifyOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (CustomerOrderHandlingInstruction.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (Alpha.encode message.reserved28)))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← CustomerOrderHandlingInstruction.decode bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved28, bytes) ← Alpha.decode 28 bytes
  pure ({ matchingEngineTime, mpId, orderId, clientSendTime, leavesQty, operatorId, operatorLocation, clientOrderId, originalClientOrderId, instrumentId, price, stopOrderTriggerPrice, size, orderExpiryDate, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, maxFloorQty, reserved28 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNotification) : (encode message).length = 160 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CustomerOrderHandlingInstruction.encode_length]

theorem encode_length_pos (message : ModifyOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerOrderHandlingInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderNotification

/-- Reserve Order Replenishment Notification: 48 bytes -/
structure ReserveOrderReplenishmentNotification where
  matchingEngineTime : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  secondaryOrderId : BitVec 64
  displayQty : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace ReserveOrderReplenishmentNotification

def encode (message : ReserveOrderReplenishmentNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (encodeUIntLE 4 message.displayQty
    ++ (Alpha.encode message.reserved16)))))

def decode (bytes : List UInt8) : Option (ReserveOrderReplenishmentNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ matchingEngineTime, instrumentId, orderId, secondaryOrderId, displayQty, reserved16 }, bytes)

@[simp] theorem encode_length (message : ReserveOrderReplenishmentNotification) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ReserveOrderReplenishmentNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReserveOrderReplenishmentNotification) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReserveOrderReplenishmentNotification

/-- Cancel Reduce Size Order Notification: 102 bytes -/
structure CancelReduceSizeOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  instrumentId : BitVec 32
  orderId : BitVec 64
  clientSendTime : BitVec 64
  leavesQty : BitVec 32
  cancelReason : CancelReason
  lastPrice : BitVec 64
  lastSize : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace CancelReduceSizeOrderNotification

def encode (message : CancelReduceSizeOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (CancelReason.encode message.cancelReason
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (Alpha.encode message.reserved8))))))))))))

def decode (bytes : List UInt8) : Option (CancelReduceSizeOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, mpId, operatorId, operatorLocation, clientOrderId, instrumentId, orderId, clientSendTime, leavesQty, cancelReason, lastPrice, lastSize, reserved8 }, bytes)

@[simp] theorem encode_length (message : CancelReduceSizeOrderNotification) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CancelReason.encode_length]

theorem encode_length_pos (message : CancelReduceSizeOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelReduceSizeOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CancelReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelReduceSizeOrderNotification

/-- Order Status Update Notification: 53 bytes -/
structure OrderStatusUpdateNotification where
  matchingEngineTime : BitVec 64
  instrumentId : BitVec 32
  orderId : BitVec 64
  updateStatus : UpdateStatus
  orderType : OrderType
  timeInForce : TimeInForce
  reserved30 : Alpha 30
  deriving DecidableEq, Repr

namespace OrderStatusUpdateNotification

def encode (message : OrderStatusUpdateNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.orderId
    ++ (UpdateStatus.encode message.updateStatus
    ++ (OrderType.encode message.orderType
    ++ (TimeInForce.encode message.timeInForce
    ++ (Alpha.encode message.reserved30))))))

def decode (bytes : List UInt8) : Option (OrderStatusUpdateNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (updateStatus, bytes) ← UpdateStatus.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (reserved30, bytes) ← Alpha.decode 30 bytes
  pure ({ matchingEngineTime, instrumentId, orderId, updateStatus, orderType, timeInForce, reserved30 }, bytes)

@[simp] theorem encode_length (message : OrderStatusUpdateNotification) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, UpdateStatus.encode_length, OrderType.encode_length, TimeInForce.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderStatusUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderStatusUpdateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, UpdateStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderStatusUpdateNotification

/-- Simple Execution Notification: 159 bytes -/
structure SimpleExecutionNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  instrumentId : BitVec 32
  clientOrderId : Alpha 20
  simpleTradeId : BitVec 64
  complexTradeId : BitVec 64
  executionId : BitVec 64
  tradeDate : BitVec 16
  correctionNumber : BitVec 8
  tradeStatus : TradeStatus
  lastPrice : BitVec 64
  lastSize : BitVec 32
  executionOrderInstructions : BitVec 16
  ctiCode : CtiCode
  textMemo : Alpha 20
  liquidityIndicator : Alpha 3
  secondaryOrderId : BitVec 64
  lastPriceRestatement : LastPriceRestatement
  reserved23 : Alpha 23
  deriving DecidableEq, Repr

namespace SimpleExecutionNotification

def encode (message : SimpleExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.simpleTradeId
    ++ (encodeUIntLE 8 message.complexTradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUInt 1 message.correctionNumber
    ++ (TradeStatus.encode message.tradeStatus
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (encodeUIntLE 2 message.executionOrderInstructions
    ++ (CtiCode.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (Alpha.encode message.liquidityIndicator
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (LastPriceRestatement.encode message.lastPriceRestatement
    ++ (Alpha.encode message.reserved23))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleExecutionNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (simpleTradeId, bytes) ← decodeUIntLE 8 bytes
  let (complexTradeId, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (correctionNumber, bytes) ← decodeUInt 1 bytes
  let (tradeStatus, bytes) ← TradeStatus.decode bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (executionOrderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (ctiCode, bytes) ← CtiCode.decode bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (liquidityIndicator, bytes) ← Alpha.decode 3 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceRestatement, bytes) ← LastPriceRestatement.decode bytes
  let (reserved23, bytes) ← Alpha.decode 23 bytes
  pure ({ matchingEngineTime, mpId, operatorId, operatorLocation, instrumentId, clientOrderId, simpleTradeId, complexTradeId, executionId, tradeDate, correctionNumber, tradeStatus, lastPrice, lastSize, executionOrderInstructions, ctiCode, textMemo, liquidityIndicator, secondaryOrderId, lastPriceRestatement, reserved23 }, bytes)

@[simp] theorem encode_length (message : SimpleExecutionNotification) : (encode message).length = 159 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, TradeStatus.encode_length, CtiCode.encode_length, LastPriceRestatement.encode_length]

theorem encode_length_pos (message : SimpleExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, TradeStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CtiCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, LastPriceRestatement.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleExecutionNotification

/-- Complex Execution Notification: 93 bytes -/
structure ComplexExecutionNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  instrumentId : BitVec 32
  clientOrderId : Alpha 20
  complexTradeId : BitVec 64
  tradeDate : BitVec 16
  lastNetPrice : BitVec 64
  lastSize : BitVec 32
  executionOrderInstructions : BitVec 16
  secondaryOrderId : BitVec 64
  lastPriceRestatement : LastPriceRestatement
  reserved23 : Alpha 23
  deriving DecidableEq, Repr

namespace ComplexExecutionNotification

def encode (message : ComplexExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.complexTradeId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.lastNetPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (encodeUIntLE 2 message.executionOrderInstructions
    ++ (encodeUIntLE 8 message.secondaryOrderId
    ++ (LastPriceRestatement.encode message.lastPriceRestatement
    ++ (Alpha.encode message.reserved23)))))))))))

def decode (bytes : List UInt8) : Option (ComplexExecutionNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (complexTradeId, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (lastNetPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (executionOrderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (secondaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (lastPriceRestatement, bytes) ← LastPriceRestatement.decode bytes
  let (reserved23, bytes) ← Alpha.decode 23 bytes
  pure ({ matchingEngineTime, mpId, instrumentId, clientOrderId, complexTradeId, tradeDate, lastNetPrice, lastSize, executionOrderInstructions, secondaryOrderId, lastPriceRestatement, reserved23 }, bytes)

@[simp] theorem encode_length (message : ComplexExecutionNotification) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, LastPriceRestatement.encode_length]

theorem encode_length_pos (message : ComplexExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, LastPriceRestatement.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | massCancelResponse (message : MassCancelResponse) -- "XR" 0x5852
  | strategyCreationResponseMessage (message : StrategyCreationResponseMessage) -- "SR" 0x5352
  | systemStateNotificationMessage (message : SystemStateNotificationMessage) -- "SN" 0x534E
  | newOrderNotification (message : NewOrderNotification) -- "O1" 0x4F31
  | modifyOrderNotification (message : ModifyOrderNotification) -- "MN" 0x4D4E
  | reserveOrderReplenishmentNotification (message : ReserveOrderReplenishmentNotification) -- "RP" 0x5250
  | cancelReduceSizeOrderNotification (message : CancelReduceSizeOrderNotification) -- "XN" 0x584E
  | orderStatusUpdateNotification (message : OrderStatusUpdateNotification) -- "OS" 0x4F53
  | simpleExecutionNotification (message : SimpleExecutionNotification) -- "EN" 0x454E
  | complexExecutionNotification (message : ComplexExecutionNotification) -- "CN" 0x434E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderResponse _ => 19794
  | .cancelOrderResponse _ => 17234
  | .massCancelResponse _ => 22610
  | .strategyCreationResponseMessage _ => 21330
  | .systemStateNotificationMessage _ => 21326
  | .newOrderNotification _ => 20273
  | .modifyOrderNotification _ => 19790
  | .reserveOrderReplenishmentNotification _ => 21072
  | .cancelReduceSizeOrderNotification _ => 22606
  | .orderStatusUpdateNotification _ => 20307
  | .simpleExecutionNotification _ => 17742
  | .complexExecutionNotification _ => 17230

def encode : SequencedMessage → List UInt8
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .massCancelResponse message => MassCancelResponse.encode message
  | .strategyCreationResponseMessage message => StrategyCreationResponseMessage.encode message
  | .systemStateNotificationMessage message => SystemStateNotificationMessage.encode message
  | .newOrderNotification message => NewOrderNotification.encode message
  | .modifyOrderNotification message => ModifyOrderNotification.encode message
  | .reserveOrderReplenishmentNotification message => ReserveOrderReplenishmentNotification.encode message
  | .cancelReduceSizeOrderNotification message => CancelReduceSizeOrderNotification.encode message
  | .orderStatusUpdateNotification message => OrderStatusUpdateNotification.encode message
  | .simpleExecutionNotification message => SimpleExecutionNotification.encode message
  | .complexExecutionNotification message => ComplexExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 190 := by
  cases message with
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [encode, MassCancelResponse.encode_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [encode, StrategyCreationResponseMessage.encode_length]
    omega
  | systemStateNotificationMessage inner =>
    simp only [encode, SystemStateNotificationMessage.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [encode, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [encode, ModifyOrderNotification.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [encode, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [encode, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderStatusUpdateNotification inner =>
    simp only [encode, OrderStatusUpdateNotification.encode_length]
    omega
  | simpleExecutionNotification inner =>
    simp only [encode, SimpleExecutionNotification.encode_length]
    omega
  | complexExecutionNotification inner =>
    simp only [encode, ComplexExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 22610 then (MassCancelResponse.decode bytes).map fun (message, rest) => (.massCancelResponse message, rest)
  else if tag = 21330 then (StrategyCreationResponseMessage.decode bytes).map fun (message, rest) => (.strategyCreationResponseMessage message, rest)
  else if tag = 21326 then (SystemStateNotificationMessage.decode bytes).map fun (message, rest) => (.systemStateNotificationMessage message, rest)
  else if tag = 20273 then (NewOrderNotification.decode bytes).map fun (message, rest) => (.newOrderNotification message, rest)
  else if tag = 19790 then (ModifyOrderNotification.decode bytes).map fun (message, rest) => (.modifyOrderNotification message, rest)
  else if tag = 21072 then (ReserveOrderReplenishmentNotification.decode bytes).map fun (message, rest) => (.reserveOrderReplenishmentNotification message, rest)
  else if tag = 22606 then (CancelReduceSizeOrderNotification.decode bytes).map fun (message, rest) => (.cancelReduceSizeOrderNotification message, rest)
  else if tag = 20307 then (OrderStatusUpdateNotification.decode bytes).map fun (message, rest) => (.orderStatusUpdateNotification message, rest)
  else if tag = 17742 then (SimpleExecutionNotification.decode bytes).map fun (message, rest) => (.simpleExecutionNotification message, rest)
  else if tag = 17230 then (ComplexExecutionNotification.decode bytes).map fun (message, rest) => (.complexExecutionNotification message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 2 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequenceNumber, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 200 := by
  unfold encode
  cases message.sequencedMessage with
  | newOrderResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, MassCancelResponse.encode_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, StrategyCreationResponseMessage.encode_length]
    omega
  | systemStateNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemStateNotificationMessage.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderNotification.encode_length]
    omega
  | reserveOrderReplenishmentNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ReserveOrderReplenishmentNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderStatusUpdateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderStatusUpdateNotification.encode_length]
    omega
  | simpleExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SimpleExecutionNotification.encode_length]
    omega
  | complexExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ComplexExecutionNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- New Order Request Message: 174 bytes -/
structure NewOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  account : Alpha 16
  clientOrderId : Alpha 20
  instrumentId : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  size : BitVec 32
  orderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : OrderType
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : CustomerOrderHandlingInstruction
  additionalOrderIndicators : BitVec 8
  minQty : BitVec 32
  orderExpiryDate : BitVec 16
  tradingCollarDollarValue : BitVec 64
  ctiCode : CtiCode
  textMemo : Alpha 20
  maxFloorQty : BitVec 32
  displayRangeQty : BitVec 32
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace NewOrderRequestMessage

def encode (message : NewOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderType.encode message.orderType
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (CustomerOrderHandlingInstruction.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (CtiCode.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (encodeUIntLE 4 message.displayRangeQty
    ++ (Alpha.encode message.reserved24)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← CustomerOrderHandlingInstruction.decode bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (ctiCode, bytes) ← CtiCode.decode bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (displayRangeQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, account, clientOrderId, instrumentId, price, stopOrderTriggerPrice, size, orderInstructions, timeInForce, orderType, selfTradeProtection, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, minQty, orderExpiryDate, tradingCollarDollarValue, ctiCode, textMemo, maxFloorQty, displayRangeQty, reserved24 }, bytes)

@[simp] theorem encode_length (message : NewOrderRequestMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TimeInForce.encode_length, OrderType.encode_length, CustomerOrderHandlingInstruction.encode_length, CtiCode.encode_length]

theorem encode_length_pos (message : NewOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerOrderHandlingInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CtiCode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderRequestMessage

/-- Modify Order Request Message: 140 bytes -/
structure ModifyOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentId : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  size : BitVec 32
  orderExpiryDate : BitVec 16
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : CustomerOrderHandlingInstruction
  additionalOrderIndicators : BitVec 8
  maxFloorQty : BitVec 32
  reserved28 : Alpha 28
  deriving DecidableEq, Repr

namespace ModifyOrderRequestMessage

def encode (message : ModifyOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (CustomerOrderHandlingInstruction.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.maxFloorQty
    ++ (Alpha.encode message.reserved28))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← CustomerOrderHandlingInstruction.decode bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (maxFloorQty, bytes) ← decodeUIntLE 4 bytes
  let (reserved28, bytes) ← Alpha.decode 28 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, clientOrderId, originalClientOrderId, instrumentId, price, stopOrderTriggerPrice, size, orderExpiryDate, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, maxFloorQty, reserved28 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderRequestMessage) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, CustomerOrderHandlingInstruction.encode_length]

theorem encode_length_pos (message : ModifyOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustomerOrderHandlingInstruction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderRequestMessage

/-- Cancel Order Request Message: 99 bytes -/
structure CancelOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  orderId : BitVec 64
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentId : BitVec 32
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderRequestMessage

def encode (message : CancelOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reserved10))))))))

def decode (bytes : List UInt8) : Option (CancelOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, orderId, clientOrderId, originalClientOrderId, instrumentId, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderRequestMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderRequestMessage

/-- Mass Cancel Request: 93 bytes -/
structure MassCancelRequest where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  reserved10 : Alpha 10
  clientOrderId : Alpha 20
  scope : Scope
  action : Action
  productGroupCode : Alpha 13
  productType : ProductType
  purgeGroup : Alpha 1
  reserved9 : Alpha 9
  deriving DecidableEq, Repr

namespace MassCancelRequest

def encode (message : MassCancelRequest) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.clientOrderId
    ++ (Scope.encode message.scope
    ++ (Action.encode message.action
    ++ (Alpha.encode message.productGroupCode
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.reserved9)))))))))))

def decode (bytes : List UInt8) : Option (MassCancelRequest × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (scope, bytes) ← Scope.decode bytes
  let (action, bytes) ← Action.decode bytes
  let (productGroupCode, bytes) ← Alpha.decode 13 bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, reserved10, clientOrderId, scope, action, productGroupCode, productType, purgeGroup, reserved9 }, bytes)

@[simp] theorem encode_length (message : MassCancelRequest) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Scope.encode_length, Action.encode_length, ProductType.encode_length]

theorem encode_length_pos (message : MassCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Scope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Action.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelRequest

/-- Strategy Leg: 16 bytes -/
structure StrategyLeg where
  instrumentId : BitVec 32
  legRatio : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyLeg

def encode (message : StrategyLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 4 message.legRatio
    ++ (Alpha.encode message.reserved8))

def decode (bytes : List UInt8) : Option (StrategyLeg × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentId, legRatio, reserved8 }, bytes)

@[simp] theorem encode_length (message : StrategyLeg) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyLeg

/-- Strategy Creation Request -/
structure StrategyCreationRequest where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  reserved16 : Alpha 16
  strategyLeg : Bounded 1 StrategyLeg
  deriving DecidableEq, Repr

namespace StrategyCreationRequest

def encode (message : StrategyCreationRequest) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.reserved16
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.strategyLeg.val.length)
    ++ (encodeMany StrategyLeg.encode message.strategyLeg.val)))))))

def decode (bytes : List UInt8) : Option (StrategyCreationRequest × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (strategyLeg_, bytes) ← decodeMany StrategyLeg.decode numberOfLegs.toNat bytes
  if fits_strategyLeg : strategyLeg_.length < 256 ^ 1 then
    pure ({ clientSendTime, mpId, operatorId, operatorLocation, clientOrderId, reserved16, strategyLeg := ⟨strategyLeg_, fits_strategyLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyCreationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyCreationRequest) : (encode message).length ≤ 4154 := by
  have bound_strategyLeg := message.strategyLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, encodeMany_length_const StrategyLeg.encode 16 StrategyLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyCreationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeMany_bounded 1 StrategyLeg.encode StrategyLeg.decode StrategyLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyLeg.length_lt]
  rfl

end StrategyCreationRequest

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | newOrderRequestMessage (message : NewOrderRequestMessage) -- "N1" 0x4E31
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderRequestMessage (message : ModifyOrderRequestMessage) -- "M1" 0x4D31
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderRequestMessage (message : CancelOrderRequestMessage) -- "CO" 0x434F
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | massCancelRequest (message : MassCancelRequest) -- "X1" 0x5831
  | massCancelResponse (message : MassCancelResponse) -- "XR" 0x5852
  | strategyCreationRequest (message : StrategyCreationRequest) -- "SD" 0x5344
  | strategyCreationResponseMessage (message : StrategyCreationResponseMessage) -- "SR" 0x5352
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .newOrderRequestMessage _ => 20017
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderRequestMessage _ => 19761
  | .modifyOrderResponse _ => 19794
  | .cancelOrderRequestMessage _ => 17231
  | .cancelOrderResponse _ => 17234
  | .massCancelRequest _ => 22577
  | .massCancelResponse _ => 22610
  | .strategyCreationRequest _ => 21316
  | .strategyCreationResponseMessage _ => 21330

def encode : UnsequencedMessage → List UInt8
  | .newOrderRequestMessage message => NewOrderRequestMessage.encode message
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderRequestMessage message => ModifyOrderRequestMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderRequestMessage message => CancelOrderRequestMessage.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .massCancelRequest message => MassCancelRequest.encode message
  | .massCancelResponse message => MassCancelResponse.encode message
  | .strategyCreationRequest message => StrategyCreationRequest.encode message
  | .strategyCreationResponseMessage message => StrategyCreationResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 4154 := by
  cases message with
  | newOrderRequestMessage inner =>
    simp only [encode, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [encode, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequestMessage inner =>
    simp only [encode, CancelOrderRequestMessage.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [encode, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [encode, MassCancelResponse.encode_length]
    omega
  | strategyCreationRequest inner =>
    have bound_inner := StrategyCreationRequest.encode_length_le inner
    simp only [encode]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [encode, StrategyCreationResponseMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 20017 then (NewOrderRequestMessage.decode bytes).map fun (message, rest) => (.newOrderRequestMessage message, rest)
  else if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19761 then (ModifyOrderRequestMessage.decode bytes).map fun (message, rest) => (.modifyOrderRequestMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17231 then (CancelOrderRequestMessage.decode bytes).map fun (message, rest) => (.cancelOrderRequestMessage message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 22577 then (MassCancelRequest.decode bytes).map fun (message, rest) => (.massCancelRequest message, rest)
  else if tag = 22610 then (MassCancelResponse.decode bytes).map fun (message, rest) => (.massCancelResponse message, rest)
  else if tag = 21316 then (StrategyCreationRequest.decode bytes).map fun (message, rest) => (.strategyCreationRequest message, rest)
  else if tag = 21330 then (StrategyCreationResponseMessage.decode bytes).map fun (message, rest) => (.strategyCreationResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 4156 := by
  unfold encode
  cases message.unsequencedMessage with
  | newOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderRequestMessage.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelResponse.encode_length]
    omega
  | strategyCreationRequest inner =>
    have bound_inner := StrategyCreationRequest.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, StrategyCreationResponseMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedSession : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedSession
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedSession, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 10 bytes -/
structure LoginResponse where
  loginStatus : LoginStatus
  sessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.sessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (sessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ loginStatus, sessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, LoginStatus.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 0 bytes -/
structure SynchronizationComplete where
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (_ : SynchronizationComplete) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 61378
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61378 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 61379 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  logoutReason : LogoutReason
  logoutText : Capped 61378
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61378 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 61379 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

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

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "L" 0x4C
  | loginResponse (message : LoginResponse) -- "R" 0x52
  | synchronizationComplete (message : SynchronizationComplete) -- "C" 0x43
  | retransmissionRequest (message : RetransmissionRequest) -- "A" 0x41
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | endOfSession (message : EndOfSession) -- "E" 0x45
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 83
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 76
  | .loginResponse _ => 82
  | .synchronizationComplete _ => 67
  | .retransmissionRequest _ => 65
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .endOfSession _ => 69
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .endOfSession message => EndOfSession.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 61379 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 76 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 82 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 67 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 65 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 69 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]

end SesmPayload

/-- Sesm Tcp Packet -/
structure SesmTcpPacket where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacket

def encodeBody (message : SesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacket := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.sesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfSession inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega

/-- Size rule: Sesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : SesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SesmTcpPacket

/-- Packet -/
structure Packet where
  sesmTcpPacket : List SesmTcpPacket
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  pure { sesmTcpPacket }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rfl

end Packet

end Omi.MiaxOnyxfuturesExpressinterfaceFeiV13A
