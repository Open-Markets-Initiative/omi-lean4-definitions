import Wire

/-!
# A2X Markets A2X Binary Protocol v2.9.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Order Add Response Status is 1 byte whichever arm the model names: the arms are bit field sets
of that width and differ only in what the bits beside Order Status are called — Order Status of 3
names Status Cancel Reason; Order Status of 4 names Status Reject Reason; any other value names
Status. It is read as that set's integer, so which naming applies is left to what is built on the
definition, as a set's members always are.

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

Note: Status is a bit field set, proven as its 1 byte integer rather than bit by bit

License: MIT No Attribution
-/

namespace Omi.A2xA2xequitiesTradingprotocolAtpV293

/-- Login Message: 40 bytes -/
structure LoginMessage where
  protocolVersion : BitVec 16
  senderId : Alpha 16
  password : Alpha 16
  inactivityTimeout : BitVec 16
  atpSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  encodeUIntLE 2 message.protocolVersion
    ++ (Alpha.encode message.senderId
    ++ (Alpha.encode message.password
    ++ (encodeUIntLE 2 message.inactivityTimeout
    ++ (encodeUIntLE 4 message.atpSeqNo))))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (protocolVersion, bytes) ← decodeUIntLE 2 bytes
  let (senderId, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (inactivityTimeout, bytes) ← decodeUIntLE 2 bytes
  let (atpSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ protocolVersion, senderId, password, inactivityTimeout, atpSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 40 := by
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

/-- Login Response Message: 5 bytes -/
structure LoginResponseMessage where
  resultCode : BitVec 8
  clientSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  encodeUInt 1 message.resultCode
    ++ (encodeUIntLE 4 message.clientSeqNo)

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (resultCode, bytes) ← decodeUInt 1 bytes
  let (clientSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ resultCode, clientSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 5 := by
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

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

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
  reserved16 : Alpha 16
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
    ++ (Alpha.encode message.reserved16)))))))))

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
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ securityIdLong, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, reserved16 }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAddMessage

/-- Order Add Extended Message: 54 bytes -/
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
  reserved16 : Alpha 16
  displayQuantity : BitVec 32
  minQty : BitVec 32
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
    ++ (Alpha.encode message.reserved16
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 4 message.minQty)))))))))))

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
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityIdLong, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, reserved16, displayQuantity, minQty }, bytes)

@[simp] theorem encode_length (message : OrderAddExtendedMessage) : (encode message).length = 54 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddExtendedMessage

/-- Order Add Response Message: 29 bytes -/
structure OrderAddResponseMessage where
  orderRef : BitVec 32
  marketDataId : BitVec 32
  orderAddResponseStatus : BitVec 8
  tradedQuantity : BitVec 32
  timestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddResponseMessage

def encode (message : OrderAddResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.marketDataId
    ++ (encodeUIntLE 1 message.orderAddResponseStatus
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag)))))

def decode (bytes : List UInt8) : Option (OrderAddResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (marketDataId, bytes) ← decodeUIntLE 4 bytes
  let (orderAddResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, marketDataId, orderAddResponseStatus, tradedQuantity, timestamp, userTag }, bytes)

@[simp] theorem encode_length (message : OrderAddResponseMessage) : (encode message).length = 29 := by
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddResponseMessage

/-- Order Cancel Message: 28 bytes -/
structure OrderCancelMessage where
  orderRef : BitVec 32
  userTag : BitVec 64
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.userTag
    ++ (Alpha.encode message.reserved16))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ orderRef, userTag, reserved16 }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelMessage

/-- Order Cancel Response Message: 25 bytes -/
structure OrderCancelResponseMessage where
  orderRef : BitVec 32
  requestRef : BitVec 32
  orderCancelResponseStatus : BitVec 8
  cancellationTimestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelResponseMessage

def encode (message : OrderCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 1 message.orderCancelResponseStatus
    ++ (encodeUIntLE 8 message.cancellationTimestamp
    ++ (encodeUIntLE 8 message.userTag))))

def decode (bytes : List UInt8) : Option (OrderCancelResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (orderCancelResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (cancellationTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, requestRef, orderCancelResponseStatus, cancellationTimestamp, userTag }, bytes)

@[simp] theorem encode_length (message : OrderCancelResponseMessage) : (encode message).length = 25 := by
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

/-- Order Modify Message: 41 bytes -/
structure OrderModifyMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  reserved16 : Alpha 16
  orderCapacity : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (Alpha.encode message.reserved16
    ++ (encodeUInt 1 message.orderCapacity)))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  pure ({ orderRef, price, quantity, userTag, reserved16, orderCapacity }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderModifyMessage

/-- Order Modify Extended Message: 45 bytes -/
structure OrderModifyExtendedMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  reserved16 : Alpha 16
  orderCapacity : BitVec 8
  displayQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderModifyExtendedMessage

def encode (message : OrderModifyExtendedMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (Alpha.encode message.reserved16
    ++ (encodeUInt 1 message.orderCapacity
    ++ (encodeUIntLE 4 message.displayQuantity))))))

def decode (bytes : List UInt8) : Option (OrderModifyExtendedMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (orderCapacity, bytes) ← decodeUInt 1 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderRef, price, quantity, userTag, reserved16, orderCapacity, displayQuantity }, bytes)

@[simp] theorem encode_length (message : OrderModifyExtendedMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyExtendedMessage

/-- Order Modify Response Message: 25 bytes -/
structure OrderModifyResponseMessage where
  orderRef : BitVec 32
  requestRef : BitVec 32
  orderModifyResponseStatus : BitVec 8
  modificationTimestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyResponseMessage

def encode (message : OrderModifyResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 1 message.orderModifyResponseStatus
    ++ (encodeUIntLE 8 message.modificationTimestamp
    ++ (encodeUIntLE 8 message.userTag))))

def decode (bytes : List UInt8) : Option (OrderModifyResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (orderModifyResponseStatus, bytes) ← decodeUIntLE 1 bytes
  let (modificationTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, requestRef, orderModifyResponseStatus, modificationTimestamp, userTag }, bytes)

@[simp] theorem encode_length (message : OrderModifyResponseMessage) : (encode message).length = 25 := by
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyResponseMessage

/-- Iceberg Order Refresh Message: 16 bytes -/
structure IcebergOrderRefreshMessage where
  orderRef : BitVec 32
  origA2xOrdId : BitVec 32
  newA2xOrdId : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace IcebergOrderRefreshMessage

def encode (message : IcebergOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.origA2xOrdId
    ++ (encodeUIntLE 4 message.newA2xOrdId
    ++ (encodeUIntLE 4 message.quantity)))

def decode (bytes : List UInt8) : Option (IcebergOrderRefreshMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (origA2xOrdId, bytes) ← decodeUIntLE 4 bytes
  let (newA2xOrdId, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderRef, origA2xOrdId, newA2xOrdId, quantity }, bytes)

@[simp] theorem encode_length (message : IcebergOrderRefreshMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IcebergOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IcebergOrderRefreshMessage) (rest : List UInt8) :
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

end IcebergOrderRefreshMessage

/-- Trade Capture Message: 48 bytes -/
structure TradeCaptureMessage where
  quantity : BitVec 32
  price : BitVec 64
  securityIdLong : BitVec 32
  tradeCaptureType : BitVec 8
  reserved1 : Alpha 1
  userTag : BitVec 64
  reserved8 : Alpha 8
  buyAccount : BitVec 16
  buyOrderCapacity : BitVec 8
  reservedLong2 : Alpha 8
  sellAccount : BitVec 16
  sellOrderCapacity : BitVec 8
  deriving DecidableEq, Repr

namespace TradeCaptureMessage

def encode (message : TradeCaptureMessage) : List UInt8 :=
  encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityIdLong
    ++ (encodeUInt 1 message.tradeCaptureType
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 8 message.userTag
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 2 message.buyAccount
    ++ (encodeUInt 1 message.buyOrderCapacity
    ++ (Alpha.encode message.reservedLong2
    ++ (encodeUIntLE 2 message.sellAccount
    ++ (encodeUInt 1 message.sellOrderCapacity)))))))))))

def decode (bytes : List UInt8) : Option (TradeCaptureMessage × List UInt8) := do
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (tradeCaptureType, bytes) ← decodeUInt 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (buyAccount, bytes) ← decodeUIntLE 2 bytes
  let (buyOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (reservedLong2, bytes) ← Alpha.decode 8 bytes
  let (sellAccount, bytes) ← decodeUIntLE 2 bytes
  let (sellOrderCapacity, bytes) ← decodeUInt 1 bytes
  pure ({ quantity, price, securityIdLong, tradeCaptureType, reserved1, userTag, reserved8, buyAccount, buyOrderCapacity, reservedLong2, sellAccount, sellOrderCapacity }, bytes)

@[simp] theorem encode_length (message : TradeCaptureMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCaptureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeCaptureMessage

/-- Trade Capture Response Message: 17 bytes -/
structure TradeCaptureResponseMessage where
  status : BitVec 8
  tradeRef : BitVec 32
  requestRef : BitVec 32
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCaptureResponseMessage

def encode (message : TradeCaptureResponseMessage) : List UInt8 :=
  encodeUIntLE 1 message.status
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 8 message.userTag)))

def decode (bytes : List UInt8) : Option (TradeCaptureResponseMessage × List UInt8) := do
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ status, tradeRef, requestRef, userTag }, bytes)

@[simp] theorem encode_length (message : TradeCaptureResponseMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCaptureResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureResponseMessage) (rest : List UInt8) :
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

end TradeCaptureResponseMessage

/-- Trade Message: 41 bytes -/
structure TradeMessage where
  orderRef : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 32
  ccpCode : BitVec 8
  liqIndicator : BitVec 8
  securityIdShort : BitVec 16
  tradeTimestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUInt 1 message.ccpCode
    ++ (encodeUInt 1 message.liqIndicator
    ++ (encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 8 message.tradeTimestamp
    ++ (encodeUIntLE 8 message.userTag)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (ccpCode, bytes) ← decodeUInt 1 bytes
  let (liqIndicator, bytes) ← decodeUInt 1 bytes
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (tradeTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, ccpCode, liqIndicator, securityIdShort, tradeTimestamp, userTag }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 41 := by
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Bust Message: 29 bytes -/
structure TradeBustMessage where
  orderRef : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 32
  bustTimestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.bustTimestamp)))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (bustTimestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, bustTimestamp }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 29 := by
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
  | heartbeat (message : Heartbeat) -- 0
  | logoutRequestMessage (message : LogoutRequestMessage) -- 3
  | logoutMessage (message : LogoutMessage) -- 4
  | orderAddMessage (message : OrderAddMessage) -- 24
  | orderAddExtendedMessage (message : OrderAddExtendedMessage) -- 25
  | orderAddResponseMessage (message : OrderAddResponseMessage) -- 6
  | orderCancelMessage (message : OrderCancelMessage) -- 7
  | orderCancelResponseMessage (message : OrderCancelResponseMessage) -- 8
  | orderModifyMessage (message : OrderModifyMessage) -- 9
  | orderModifyExtendedMessage (message : OrderModifyExtendedMessage) -- 22
  | orderModifyResponseMessage (message : OrderModifyResponseMessage) -- 10
  | icebergOrderRefreshMessage (message : IcebergOrderRefreshMessage) -- 23
  | tradeCaptureMessage (message : TradeCaptureMessage) -- 26
  | tradeCaptureResponseMessage (message : TradeCaptureResponseMessage) -- 18
  | tradeMessage (message : TradeMessage) -- 11
  | tradeBustMessage (message : TradeBustMessage) -- 12
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginMessage _ => 1
  | .loginResponseMessage _ => 2
  | .heartbeat _ => 0
  | .logoutRequestMessage _ => 3
  | .logoutMessage _ => 4
  | .orderAddMessage _ => 24
  | .orderAddExtendedMessage _ => 25
  | .orderAddResponseMessage _ => 6
  | .orderCancelMessage _ => 7
  | .orderCancelResponseMessage _ => 8
  | .orderModifyMessage _ => 9
  | .orderModifyExtendedMessage _ => 22
  | .orderModifyResponseMessage _ => 10
  | .icebergOrderRefreshMessage _ => 23
  | .tradeCaptureMessage _ => 26
  | .tradeCaptureResponseMessage _ => 18
  | .tradeMessage _ => 11
  | .tradeBustMessage _ => 12

def encode : Payload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .logoutRequestMessage message => LogoutRequestMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderAddExtendedMessage message => OrderAddExtendedMessage.encode message
  | .orderAddResponseMessage message => OrderAddResponseMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderCancelResponseMessage message => OrderCancelResponseMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderModifyExtendedMessage message => OrderModifyExtendedMessage.encode message
  | .orderModifyResponseMessage message => OrderModifyResponseMessage.encode message
  | .icebergOrderRefreshMessage message => IcebergOrderRefreshMessage.encode message
  | .tradeCaptureMessage message => TradeCaptureMessage.encode message
  | .tradeCaptureResponseMessage message => TradeCaptureResponseMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 54 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
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
  | orderAddResponseMessage inner =>
    simp only [encode, OrderAddResponseMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [encode, OrderCancelResponseMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [encode, OrderModifyMessage.encode_length]
    omega
  | orderModifyExtendedMessage inner =>
    simp only [encode, OrderModifyExtendedMessage.encode_length]
    omega
  | orderModifyResponseMessage inner =>
    simp only [encode, OrderModifyResponseMessage.encode_length]
    omega
  | icebergOrderRefreshMessage inner =>
    simp only [encode, IcebergOrderRefreshMessage.encode_length]
    omega
  | tradeCaptureMessage inner =>
    simp only [encode, TradeCaptureMessage.encode_length]
    omega
  | tradeCaptureResponseMessage inner =>
    simp only [encode, TradeCaptureResponseMessage.encode_length]
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
  else if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 3 then (LogoutRequestMessage.decode bytes).map fun (message, rest) => (.logoutRequestMessage message, rest)
  else if tag = 4 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 24 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 25 then (OrderAddExtendedMessage.decode bytes).map fun (message, rest) => (.orderAddExtendedMessage message, rest)
  else if tag = 6 then (OrderAddResponseMessage.decode bytes).map fun (message, rest) => (.orderAddResponseMessage message, rest)
  else if tag = 7 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 8 then (OrderCancelResponseMessage.decode bytes).map fun (message, rest) => (.orderCancelResponseMessage message, rest)
  else if tag = 9 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 22 then (OrderModifyExtendedMessage.decode bytes).map fun (message, rest) => (.orderModifyExtendedMessage message, rest)
  else if tag = 10 then (OrderModifyResponseMessage.decode bytes).map fun (message, rest) => (.orderModifyResponseMessage message, rest)
  else if tag = 23 then (IcebergOrderRefreshMessage.decode bytes).map fun (message, rest) => (.icebergOrderRefreshMessage message, rest)
  else if tag = 26 then (TradeCaptureMessage.decode bytes).map fun (message, rest) => (.tradeCaptureMessage message, rest)
  else if tag = 18 then (TradeCaptureResponseMessage.decode bytes).map fun (message, rest) => (.tradeCaptureResponseMessage message, rest)
  else if tag = 11 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 12 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 4 message.msgSeqNo
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (msgSeqNo, bytes) ← decodeUIntLE 4 bytes
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
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, Heartbeat.encode_length]
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
  | orderAddResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddResponseMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelResponseMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyMessage.encode_length]
    omega
  | orderModifyExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyExtendedMessage.encode_length]
    omega
  | orderModifyResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyResponseMessage.encode_length]
    omega
  | icebergOrderRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, IcebergOrderRefreshMessage.encode_length]
    omega
  | tradeCaptureMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeCaptureMessage.encode_length]
    omega
  | tradeCaptureResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeCaptureResponseMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeBustMessage.encode_length]
    omega

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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

end Omi.A2xA2xequitiesTradingprotocolAtpV293
