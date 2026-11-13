import Wire

/-!
# AsiaNext Aquis Trading Protocol v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Table Select 1 is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Table Select 2 is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Table Select 3 is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Extended Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

Note: Order Add Response Status is 1 byte whichever arm the model names: the arms are bit field sets
of that width and differ only in what the bits beside Order Status are called — Order Status of 3
names Status Cancel Reason; Order Status of 4 names Status Reject Reason; any other value names
Status. It is read as that set's integer, so which naming applies is left to what is built on the
definition, as a set's members always are.

Note: Order Add Response Flags is a bit field set, proven as its 1 byte integer rather than bit by
bit

Note: Order Cancel Response Status is 1 byte whichever arm the model names: the arms are bit field
sets of that width and differ only in what the bits beside Order Status are called — Order Status of
3 names Status Cancel Reason; Order Status of 4 names Status Reject Reason; any other value names
Status. It is read as that set's integer, so which naming applies is left to what is built on the
definition, as a set's members always are.

Note: Order Modify Response Status is 1 byte whichever arm the model names: the arms are bit field
sets of that width and differ only in what the bits beside Order Status are called — Order Status of
4 names Status Reject Reason; any other value names Status Modification Reason. It is read as that
set's integer, so which naming applies is left to what is built on the definition, as a set's
members always are.

Note: Order Modify Response Flags is a bit field set, proven as its 1 byte integer rather than bit
by bit

Note: Trade Flags is a bit field set, proven as its 1 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.AsianextAsianextderivativesTradingprotocolAtpV12

/-- Login Message: 44 bytes -/
structure LoginMessage where
  protocolVersion : BitVec 16
  senderId : Alpha 16
  password : Alpha 16
  inactivityTimeout : BitVec 16
  atpSeqNo : BitVec 64
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  encodeUIntLE 2 message.protocolVersion
    ++ (Alpha.encode message.senderId
    ++ (Alpha.encode message.password
    ++ (encodeUIntLE 2 message.inactivityTimeout
    ++ (encodeUIntLE 8 message.atpSeqNo))))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (protocolVersion, bytes) ← decodeUIntLE 2 bytes
  let (senderId, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (inactivityTimeout, bytes) ← decodeUIntLE 2 bytes
  let (atpSeqNo, bytes) ← decodeUIntLE 8 bytes
  pure ({ protocolVersion, senderId, password, inactivityTimeout, atpSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LoginMessage

/-- Login Response Message: 9 bytes -/
structure LoginResponseMessage where
  resultCode : BitVec 8
  clientSeqNo : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  encodeUInt 1 message.resultCode
    ++ (encodeUIntLE 8 message.clientSeqNo)

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (resultCode, bytes) ← decodeUInt 1 bytes
  let (clientSeqNo, bytes) ← decodeUIntLE 8 bytes
  pure ({ resultCode, clientSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LoginResponseMessage

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

/-- Logout Request Message: 0 bytes -/
structure LogoutRequestMessage where
  deriving DecidableEq, Repr

namespace LogoutRequestMessage

def encode (_ : LogoutRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequestMessage

/-- Logout Message: 33 bytes -/
structure LogoutMessage where
  logoutReasonCode : BitVec 8
  reasonText : Alpha 32
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 1 message.logoutReasonCode
    ++ (Alpha.encode message.reasonText)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (logoutReasonCode, bytes) ← decodeUInt 1 bytes
  let (reasonText, bytes) ← Alpha.decode 32 bytes
  pure ({ logoutReasonCode, reasonText }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Order Add Message: 46 bytes -/
structure OrderAddMessage where
  securityIdLong : BitVec 32
  orderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderCapacity : BitVec 8
  account : BitVec 16
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityIdLong
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.orderCapacity
    ++ (encodeUIntLE 2 message.account
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← decodeUIntLE 2 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityIdLong, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3 }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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

end OrderAddMessage

/-- Order Add Extended Message: 71 bytes -/
structure OrderAddExtendedMessage where
  securityIdLong : BitVec 32
  orderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderCapacity : BitVec 8
  account : BitVec 16
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  displayQuantity : BitVec 32
  minQty : BitVec 32
  extendedOrderFlags : BitVec 8
  expireTime : BitVec 64
  rfqSessionId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddExtendedMessage

def encode (message : OrderAddExtendedMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityIdLong
    ++ (encodeUInt 1 message.orderType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.orderCapacity
    ++ (encodeUIntLE 2 message.account
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 1 message.extendedOrderFlags
    ++ (encodeUIntLE 8 message.expireTime
    ++ (encodeUIntLE 8 message.rfqSessionId))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAddExtendedMessage × List UInt8) := do
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (orderType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← decodeUIntLE 2 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (extendedOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (rfqSessionId, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityIdLong, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, displayQuantity, minQty, extendedOrderFlags, expireTime, rfqSessionId }, bytes)

@[simp] theorem encode_length (message : OrderAddExtendedMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderAddExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddExtendedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddExtendedMessage

/-- Order Cancel Message: 32 bytes -/
structure OrderCancelMessage where
  orderRef : BitVec 64
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3))))))))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderRef, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3 }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelMessage

/-- Order Modify Message: 45 bytes -/
structure OrderModifyMessage where
  orderRef : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  orderCapacity : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUInt 1 message.orderCapacity)))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  pure ({ orderRef, price, quantity, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, orderCapacity }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderModifyMessage

/-- Order Modify Extended Message: 61 bytes -/
structure OrderModifyExtendedMessage where
  orderRef : BitVec 64
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  orderCapacity : BitVec 8
  displayQuantity : BitVec 32
  minQty : BitVec 32
  expireTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyExtendedMessage

def encode (message : OrderModifyExtendedMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUInt 1 message.orderCapacity
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 8 message.expireTime))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyExtendedMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, price, quantity, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, orderCapacity, displayQuantity, minQty, expireTime }, bytes)

@[simp] theorem encode_length (message : OrderModifyExtendedMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderModifyExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyExtendedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyExtendedMessage

/-- Order Add Response Message: 38 bytes -/
structure OrderAddResponseMessage where
  orderRef : BitVec 64
  marketDataId : BitVec 64
  orderAddResponseStatus : BitVec 8
  tradedQuantity : BitVec 32
  timestamp : BitVec 64
  userTag : BitVec 64
  orderAddResponseFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderAddResponseMessage

def encode (message : OrderAddResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.marketDataId
    ++ (encodeUIntLE 1 message.orderAddResponseStatus
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.orderAddResponseFlags))))))

def decode (bytes : List UInt8) : Option (OrderAddResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (marketDataId, bytes) ← decodeUIntLE 8 bytes
  let (orderAddResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (orderAddResponseFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, marketDataId, orderAddResponseStatus, tradedQuantity, timestamp, userTag, orderAddResponseFlags }, bytes)

@[simp] theorem encode_length (message : OrderAddResponseMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddResponseMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddResponseMessage

/-- Order Cancel Response Message: 33 bytes -/
structure OrderCancelResponseMessage where
  orderRef : BitVec 64
  requestRef : BitVec 64
  orderCancelResponseStatus : BitVec 8
  timestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelResponseMessage

def encode (message : OrderCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.requestRef
    ++ (encodeUIntLE 1 message.orderCancelResponseStatus
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag))))

def decode (bytes : List UInt8) : Option (OrderCancelResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (requestRef, bytes) ← decodeUIntLE 8 bytes
  let (orderCancelResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, requestRef, orderCancelResponseStatus, timestamp, userTag }, bytes)

@[simp] theorem encode_length (message : OrderCancelResponseMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelResponseMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelResponseMessage

/-- Order Modify Response Message: 34 bytes -/
structure OrderModifyResponseMessage where
  orderRef : BitVec 64
  requestRef : BitVec 64
  orderModifyResponseStatus : BitVec 8
  timestamp : BitVec 64
  userTag : BitVec 64
  orderModifyResponseFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyResponseMessage

def encode (message : OrderModifyResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 8 message.requestRef
    ++ (encodeUIntLE 1 message.orderModifyResponseStatus
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.orderModifyResponseFlags)))))

def decode (bytes : List UInt8) : Option (OrderModifyResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (requestRef, bytes) ← decodeUIntLE 8 bytes
  let (orderModifyResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (orderModifyResponseFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, requestRef, orderModifyResponseStatus, timestamp, userTag, orderModifyResponseFlags }, bytes)

@[simp] theorem encode_length (message : OrderModifyResponseMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyResponseMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyResponseMessage

/-- Quote Request Message: 37 bytes -/
structure QuoteRequestMessage where
  securityIdLong : BitVec 32
  quantity : BitVec 32
  side : BitVec 8
  userTag : BitVec 64
  marketMakerCode1 : Alpha 4
  marketMakerCode2 : Alpha 4
  marketMakerCode3 : Alpha 4
  marketMakerCode4 : Alpha 4
  marketMakerCode5 : Alpha 4
  deriving DecidableEq, Repr

namespace QuoteRequestMessage

def encode (message : QuoteRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.securityIdLong
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 8 message.userTag
    ++ (Alpha.encode message.marketMakerCode1
    ++ (Alpha.encode message.marketMakerCode2
    ++ (Alpha.encode message.marketMakerCode3
    ++ (Alpha.encode message.marketMakerCode4
    ++ (Alpha.encode message.marketMakerCode5))))))))

def decode (bytes : List UInt8) : Option (QuoteRequestMessage × List UInt8) := do
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (marketMakerCode1, bytes) ← Alpha.decode 4 bytes
  let (marketMakerCode2, bytes) ← Alpha.decode 4 bytes
  let (marketMakerCode3, bytes) ← Alpha.decode 4 bytes
  let (marketMakerCode4, bytes) ← Alpha.decode 4 bytes
  let (marketMakerCode5, bytes) ← Alpha.decode 4 bytes
  pure ({ securityIdLong, quantity, side, userTag, marketMakerCode1, marketMakerCode2, marketMakerCode3, marketMakerCode4, marketMakerCode5 }, bytes)

@[simp] theorem encode_length (message : QuoteRequestMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestMessage) (rest : List UInt8) :
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

end QuoteRequestMessage

/-- Quote Request Notification Message: 35 bytes -/
structure QuoteRequestNotificationMessage where
  rfqSessionId : BitVec 64
  securityIdLong : BitVec 32
  quantity : BitVec 32
  side : BitVec 8
  quoteRequestStatus : BitVec 8
  statusDetails : BitVec 8
  msgRef : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteRequestNotificationMessage

def encode (message : QuoteRequestNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.rfqSessionId
    ++ (encodeUIntLE 4 message.securityIdLong
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.quoteRequestStatus
    ++ (encodeUInt 1 message.statusDetails
    ++ (encodeUIntLE 8 message.msgRef
    ++ (encodeUIntLE 8 message.userTag)))))))

def decode (bytes : List UInt8) : Option (QuoteRequestNotificationMessage × List UInt8) := do
  let (rfqSessionId, bytes) ← decodeUIntLE 8 bytes
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quoteRequestStatus, bytes) ← decodeUInt 1 bytes
  let (statusDetails, bytes) ← decodeUInt 1 bytes
  let (msgRef, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ rfqSessionId, securityIdLong, quantity, side, quoteRequestStatus, statusDetails, msgRef, userTag }, bytes)

@[simp] theorem encode_length (message : QuoteRequestNotificationMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteRequestNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteRequestNotificationMessage

/-- Quote Add Message: 31 bytes -/
structure QuoteAddMessage where
  aqxOrderId : BitVec 64
  securityIdShort : BitVec 16
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  rfqSessionId : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteAddMessage

def encode (message : QuoteAddMessage) : List UInt8 :=
  encodeUIntLE 8 message.aqxOrderId
    ++ (encodeUIntLE 2 message.securityIdShort
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.rfqSessionId)))))

def decode (bytes : List UInt8) : Option (QuoteAddMessage × List UInt8) := do
  let (aqxOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (rfqSessionId, bytes) ← decodeUIntLE 8 bytes
  pure ({ aqxOrderId, securityIdShort, side, quantity, price, rfqSessionId }, bytes)

@[simp] theorem encode_length (message : QuoteAddMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAddMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAddMessage

/-- Quote Modify Message: 22 bytes -/
structure QuoteModifyMessage where
  aqxOrderId : BitVec 64
  securityIdShort : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteModifyMessage

def encode (message : QuoteModifyMessage) : List UInt8 :=
  encodeUIntLE 8 message.aqxOrderId
    ++ (encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price)))

def decode (bytes : List UInt8) : Option (QuoteModifyMessage × List UInt8) := do
  let (aqxOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ aqxOrderId, securityIdShort, quantity, price }, bytes)

@[simp] theorem encode_length (message : QuoteModifyMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteModifyMessage) (rest : List UInt8) :
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

end QuoteModifyMessage

/-- Quote Cancel Message: 10 bytes -/
structure QuoteCancelMessage where
  aqxOrderId : BitVec 64
  securityIdShort : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteCancelMessage

def encode (message : QuoteCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.aqxOrderId
    ++ (encodeUIntLE 2 message.securityIdShort)

def decode (bytes : List UInt8) : Option (QuoteCancelMessage × List UInt8) := do
  let (aqxOrderId, bytes) ← decodeUIntLE 8 bytes
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  pure ({ aqxOrderId, securityIdShort }, bytes)

@[simp] theorem encode_length (message : QuoteCancelMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteCancelMessage

/-- Trade Message: 52 bytes -/
structure TradeMessage where
  orderRef : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 64
  ccpCode : BitVec 8
  liqIndicator : BitVec 8
  securityIdLong : BitVec 32
  timestamp : BitVec 64
  userTag : BitVec 64
  tradeFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 8 message.tradeRef
    ++ (encodeUInt 1 message.ccpCode
    ++ (encodeUInt 1 message.liqIndicator
    ++ (encodeUIntLE 4 message.securityIdLong
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.tradeFlags))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 8 bytes
  let (ccpCode, bytes) ← decodeUInt 1 bytes
  let (liqIndicator, bytes) ← decodeUInt 1 bytes
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (tradeFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, ccpCode, liqIndicator, securityIdLong, timestamp, userTag, tradeFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Bust Message: 37 bytes -/
structure TradeBustMessage where
  orderRef : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 64
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 8 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 8 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp)))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 8 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, timestamp }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBustMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | loginMessage (message : LoginMessage) -- 1
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | heartbeatMessage (message : HeartbeatMessage) -- 0
  | logoutRequestMessage (message : LogoutRequestMessage) -- 3
  | logoutMessage (message : LogoutMessage) -- 4
  | orderAddMessage (message : OrderAddMessage) -- 5
  | orderAddExtendedMessage (message : OrderAddExtendedMessage) -- 21
  | orderCancelMessage (message : OrderCancelMessage) -- 7
  | orderModifyMessage (message : OrderModifyMessage) -- 9
  | orderModifyExtendedMessage (message : OrderModifyExtendedMessage) -- 22
  | orderAddResponseMessage (message : OrderAddResponseMessage) -- 6
  | orderCancelResponseMessage (message : OrderCancelResponseMessage) -- 8
  | orderModifyResponseMessage (message : OrderModifyResponseMessage) -- 10
  | quoteRequestMessage (message : QuoteRequestMessage) -- 30
  | quoteRequestNotificationMessage (message : QuoteRequestNotificationMessage) -- 31
  | quoteAddMessage (message : QuoteAddMessage) -- 13
  | quoteModifyMessage (message : QuoteModifyMessage) -- 14
  | quoteCancelMessage (message : QuoteCancelMessage) -- 15
  | tradeMessage (message : TradeMessage) -- 11
  | tradeBustMessage (message : TradeBustMessage) -- 12
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginMessage _ => 1
  | .loginResponseMessage _ => 2
  | .heartbeatMessage _ => 0
  | .logoutRequestMessage _ => 3
  | .logoutMessage _ => 4
  | .orderAddMessage _ => 5
  | .orderAddExtendedMessage _ => 21
  | .orderCancelMessage _ => 7
  | .orderModifyMessage _ => 9
  | .orderModifyExtendedMessage _ => 22
  | .orderAddResponseMessage _ => 6
  | .orderCancelResponseMessage _ => 8
  | .orderModifyResponseMessage _ => 10
  | .quoteRequestMessage _ => 30
  | .quoteRequestNotificationMessage _ => 31
  | .quoteAddMessage _ => 13
  | .quoteModifyMessage _ => 14
  | .quoteCancelMessage _ => 15
  | .tradeMessage _ => 11
  | .tradeBustMessage _ => 12

def encode : Payload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .logoutRequestMessage message => LogoutRequestMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderAddExtendedMessage message => OrderAddExtendedMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderModifyExtendedMessage message => OrderModifyExtendedMessage.encode message
  | .orderAddResponseMessage message => OrderAddResponseMessage.encode message
  | .orderCancelResponseMessage message => OrderCancelResponseMessage.encode message
  | .orderModifyResponseMessage message => OrderModifyResponseMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .quoteRequestNotificationMessage message => QuoteRequestNotificationMessage.encode message
  | .quoteAddMessage message => QuoteAddMessage.encode message
  | .quoteModifyMessage message => QuoteModifyMessage.encode message
  | .quoteCancelMessage message => QuoteCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 71 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | logoutRequestMessage inner =>
    simp only [encode, LogoutRequestMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [encode, OrderAddMessage.encode_length]
    omega
  | orderAddExtendedMessage inner =>
    simp only [encode, OrderAddExtendedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [encode, OrderModifyMessage.encode_length]
    omega
  | orderModifyExtendedMessage inner =>
    simp only [encode, OrderModifyExtendedMessage.encode_length]
    omega
  | orderAddResponseMessage inner =>
    simp only [encode, OrderAddResponseMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [encode, OrderCancelResponseMessage.encode_length]
    omega
  | orderModifyResponseMessage inner =>
    simp only [encode, OrderModifyResponseMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [encode, QuoteRequestMessage.encode_length]
    omega
  | quoteRequestNotificationMessage inner =>
    simp only [encode, QuoteRequestNotificationMessage.encode_length]
    omega
  | quoteAddMessage inner =>
    simp only [encode, QuoteAddMessage.encode_length]
    omega
  | quoteModifyMessage inner =>
    simp only [encode, QuoteModifyMessage.encode_length]
    omega
  | quoteCancelMessage inner =>
    simp only [encode, QuoteCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [encode, TradeBustMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 0 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 3 then (LogoutRequestMessage.decode bytes).map fun (message, rest) => (.logoutRequestMessage message, rest)
  else if tag = 4 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 5 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 21 then (OrderAddExtendedMessage.decode bytes).map fun (message, rest) => (.orderAddExtendedMessage message, rest)
  else if tag = 7 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 9 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 22 then (OrderModifyExtendedMessage.decode bytes).map fun (message, rest) => (.orderModifyExtendedMessage message, rest)
  else if tag = 6 then (OrderAddResponseMessage.decode bytes).map fun (message, rest) => (.orderAddResponseMessage message, rest)
  else if tag = 8 then (OrderCancelResponseMessage.decode bytes).map fun (message, rest) => (.orderCancelResponseMessage message, rest)
  else if tag = 10 then (OrderModifyResponseMessage.decode bytes).map fun (message, rest) => (.orderModifyResponseMessage message, rest)
  else if tag = 30 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 31 then (QuoteRequestNotificationMessage.decode bytes).map fun (message, rest) => (.quoteRequestNotificationMessage message, rest)
  else if tag = 13 then (QuoteAddMessage.decode bytes).map fun (message, rest) => (.quoteAddMessage message, rest)
  else if tag = 14 then (QuoteModifyMessage.decode bytes).map fun (message, rest) => (.quoteModifyMessage message, rest)
  else if tag = 15 then (QuoteCancelMessage.decode bytes).map fun (message, rest) => (.quoteCancelMessage message, rest)
  else if tag = 11 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 12 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNo : BitVec 64
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 8 message.msgSeqNo
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (msgSeqNo, bytes) ← decodeUIntLE 8 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSeqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | loginMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LoginMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LoginResponseMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | logoutRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LogoutRequestMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddMessage.encode_length]
    omega
  | orderAddExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddExtendedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyMessage.encode_length]
    omega
  | orderModifyExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyExtendedMessage.encode_length]
    omega
  | orderAddResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddResponseMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelResponseMessage.encode_length]
    omega
  | orderModifyResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyResponseMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, QuoteRequestMessage.encode_length]
    omega
  | quoteRequestNotificationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, QuoteRequestNotificationMessage.encode_length]
    omega
  | quoteAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, QuoteAddMessage.encode_length]
    omega
  | quoteModifyMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, QuoteModifyMessage.encode_length]
    omega
  | quoteCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, QuoteCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeBustMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.AsianextAsianextderivativesTradingprotocolAtpV12
