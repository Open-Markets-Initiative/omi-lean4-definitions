import Wire

/-!
# Shanghai Stock Exchange Market Data Gateway v0.63

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.

Note: Market Data Snapshot Extension Fields is selected by more than one code: each is a constructor
of its own over the one record, so the code read is the code written back

Note: Tick-by-Tick Order Market Data Extension Fields is selected by more than one code: each is a
constructor of its own over the one record, so the code read is the code written back

Note: Binary Message is not framed: its size rule is not the length plus a constant the frame proof
covers

License: MIT No Attribution
-/

namespace Omi.SseSsesecuritiesMdgwIs120V063

/-- EndOfChannel: one byte code -/
def Endofchannel.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Endofchannel where
  | marketDataUpdatesHaveEnded -- Market data updates have ended
  | marketDataUpdatesHaveNotEnded -- Market data updates have not ended
  | unlisted (byte : { byte : UInt8 // byte ∉ Endofchannel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Endofchannel

def toByte : Endofchannel → UInt8
  | .marketDataUpdatesHaveEnded => 0x59
  | .marketDataUpdatesHaveNotEnded => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Endofchannel :=
  if byte = 0x59 then .marketDataUpdatesHaveEnded
  else .marketDataUpdatesHaveNotEnded

def ofByte (byte : UInt8) : Endofchannel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Endofchannel) : ofByte value.toByte = value := by
  cases value with
  | marketDataUpdatesHaveEnded => decide
  | marketDataUpdatesHaveNotEnded => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Endofchannel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Endofchannel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Endofchannel) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Endofchannel) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Endofchannel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Endofchannel

/-- ExecType: one byte code -/
def Exectype.codes : List UInt8 :=
  [0x30, 0x34, 0x46]

inductive Exectype where
  | newOrder -- New order
  | deleteOrder -- Delete order
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ Exectype.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Exectype

def toByte : Exectype → UInt8
  | .newOrder => 0x30
  | .deleteOrder => 0x34
  | .trade => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Exectype :=
  if byte = 0x30 then .newOrder
  else if byte = 0x34 then .deleteOrder
  else .trade

def ofByte (byte : UInt8) : Exectype :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Exectype) : ofByte value.toByte = value := by
  cases value with
  | newOrder => decide
  | deleteOrder => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Exectype) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Exectype × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Exectype) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Exectype) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Exectype) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Exectype

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Logon Message: 74 bytes -/
structure LogonMessage where
  sendercompid : Alpha 32
  targetcompid : Alpha 32
  heartbtint : BitVec 16
  applverid : Alpha 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.sendercompid
    ++ (Alpha.encode message.targetcompid
    ++ (encodeUInt 2 message.heartbtint
    ++ (Alpha.encode message.applverid)))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (sendercompid, bytes) ← Alpha.decode 32 bytes
  let (targetcompid, bytes) ← Alpha.decode 32 bytes
  let (heartbtint, bytes) ← decodeUInt 2 bytes
  let (applverid, bytes) ← Alpha.decode 8 bytes
  pure ({ sendercompid, targetcompid, heartbtint, applverid }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonMessage

/-- Logout Message: 260 bytes -/
structure LogoutMessage where
  sessionstatus : BitVec 32
  text : Alpha 256
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUInt 4 message.sessionstatus
    ++ (Alpha.encode message.text)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (sessionstatus, bytes) ← decodeUInt 4 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  pure ({ sessionstatus, text }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 260 := by
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

/-- Channel Heartbeat: 12 bytes -/
structure ChannelHeartbeat where
  channelHeartbeatSecuritytype : BitVec 8
  channelHeartbeatChannelno : BitVec 16
  appllastseqnum : BitVec 64
  endofchannel : Endofchannel
  deriving DecidableEq, Repr

namespace ChannelHeartbeat

def encode (message : ChannelHeartbeat) : List UInt8 :=
  encodeUInt 1 message.channelHeartbeatSecuritytype
    ++ (encodeUInt 2 message.channelHeartbeatChannelno
    ++ (encodeUInt 8 message.appllastseqnum
    ++ (Endofchannel.encode message.endofchannel)))

def decode (bytes : List UInt8) : Option (ChannelHeartbeat × List UInt8) := do
  let (channelHeartbeatSecuritytype, bytes) ← decodeUInt 1 bytes
  let (channelHeartbeatChannelno, bytes) ← decodeUInt 2 bytes
  let (appllastseqnum, bytes) ← decodeUInt 8 bytes
  let (endofchannel, bytes) ← Endofchannel.decode bytes
  pure ({ channelHeartbeatSecuritytype, channelHeartbeatChannelno, appllastseqnum, endofchannel }, bytes)

@[simp] theorem encode_length (message : ChannelHeartbeat) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Endofchannel.encode_length]

theorem encode_length_pos (message : ChannelHeartbeat) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ChannelHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Endofchannel.decode_encode, some_bind]
  rfl

end ChannelHeartbeat

/-- Retransmission Message: 52 bytes -/
structure RetransmissionMessage where
  retransmissionMessageChannelno : BitVec 16
  resendtype : BitVec 8
  applbegseqnum : BitVec 64
  applendseqnum : BitVec 64
  resendstatus : BitVec 8
  rejecttext : Alpha 32
  deriving DecidableEq, Repr

namespace RetransmissionMessage

def encode (message : RetransmissionMessage) : List UInt8 :=
  encodeUInt 2 message.retransmissionMessageChannelno
    ++ (encodeUInt 1 message.resendtype
    ++ (encodeUInt 8 message.applbegseqnum
    ++ (encodeUInt 8 message.applendseqnum
    ++ (encodeUInt 1 message.resendstatus
    ++ (Alpha.encode message.rejecttext)))))

def decode (bytes : List UInt8) : Option (RetransmissionMessage × List UInt8) := do
  let (retransmissionMessageChannelno, bytes) ← decodeUInt 2 bytes
  let (resendtype, bytes) ← decodeUInt 1 bytes
  let (applbegseqnum, bytes) ← decodeUInt 8 bytes
  let (applendseqnum, bytes) ← decodeUInt 8 bytes
  let (resendstatus, bytes) ← decodeUInt 1 bytes
  let (rejecttext, bytes) ← Alpha.decode 32 bytes
  pure ({ retransmissionMessageChannelno, resendtype, applbegseqnum, applendseqnum, resendstatus, rejecttext }, bytes)

@[simp] theorem encode_length (message : RetransmissionMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RetransmissionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionMessage) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmissionMessage

/-- Market Status Message: 14 bytes -/
structure MarketStatusMessage where
  marketStatusMessageSecuritytype : BitVec 8
  tradsesmode : BitVec 8
  tradingsessionid : Alpha 8
  totnorelatedsym : BitVec 32
  deriving DecidableEq, Repr

namespace MarketStatusMessage

def encode (message : MarketStatusMessage) : List UInt8 :=
  encodeUInt 1 message.marketStatusMessageSecuritytype
    ++ (encodeUInt 1 message.tradsesmode
    ++ (Alpha.encode message.tradingsessionid
    ++ (encodeUInt 4 message.totnorelatedsym)))

def decode (bytes : List UInt8) : Option (MarketStatusMessage × List UInt8) := do
  let (marketStatusMessageSecuritytype, bytes) ← decodeUInt 1 bytes
  let (tradsesmode, bytes) ← decodeUInt 1 bytes
  let (tradingsessionid, bytes) ← Alpha.decode 8 bytes
  let (totnorelatedsym, bytes) ← decodeUInt 4 bytes
  pure ({ marketStatusMessageSecuritytype, tradsesmode, tradingsessionid, totnorelatedsym }, bytes)

@[simp] theorem encode_length (message : MarketStatusMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MarketStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketStatusMessage

/-- Index Market Data Snapshot Entries: 10 bytes -/
structure IndexMarketDataSnapshotEntries where
  indexMarketDataSnapshotEntriesMdentrytype : Alpha 2
  indexMarketDataSnapshotEntriesMdentrypx : BitVec 64
  deriving DecidableEq, Repr

namespace IndexMarketDataSnapshotEntries

def encode (message : IndexMarketDataSnapshotEntries) : List UInt8 :=
  Alpha.encode message.indexMarketDataSnapshotEntriesMdentrytype
    ++ (encodeUInt 8 message.indexMarketDataSnapshotEntriesMdentrypx)

def decode (bytes : List UInt8) : Option (IndexMarketDataSnapshotEntries × List UInt8) := do
  let (indexMarketDataSnapshotEntriesMdentrytype, bytes) ← Alpha.decode 2 bytes
  let (indexMarketDataSnapshotEntriesMdentrypx, bytes) ← decodeUInt 8 bytes
  pure ({ indexMarketDataSnapshotEntriesMdentrytype, indexMarketDataSnapshotEntriesMdentrypx }, bytes)

@[simp] theorem encode_length (message : IndexMarketDataSnapshotEntries) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IndexMarketDataSnapshotEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexMarketDataSnapshotEntries) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IndexMarketDataSnapshotEntries

/-- Index Market Data Snapshot Extension Fields -/
structure IndexMarketDataSnapshotExtensionFields where
  indexMarketDataSnapshotEntries : Bounded 2 IndexMarketDataSnapshotEntries
  deriving DecidableEq, Repr

namespace IndexMarketDataSnapshotExtensionFields

def encode (message : IndexMarketDataSnapshotExtensionFields) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.indexMarketDataSnapshotEntries.val.length)
    ++ (encodeMany IndexMarketDataSnapshotEntries.encode message.indexMarketDataSnapshotEntries.val)

def decode (bytes : List UInt8) : Option (IndexMarketDataSnapshotExtensionFields × List UInt8) := do
  let (nomdentries, bytes) ← decodeUInt 2 bytes
  let (indexMarketDataSnapshotEntries_, bytes) ← decodeMany IndexMarketDataSnapshotEntries.decode nomdentries.toNat bytes
  if fits_indexMarketDataSnapshotEntries : indexMarketDataSnapshotEntries_.length < 256 ^ 2 then
    pure ({ indexMarketDataSnapshotEntries := ⟨indexMarketDataSnapshotEntries_, fits_indexMarketDataSnapshotEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : IndexMarketDataSnapshotExtensionFields) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IndexMarketDataSnapshotExtensionFields) : (encode message).length ≤ 655352 := by
  have bound_indexMarketDataSnapshotEntries := message.indexMarketDataSnapshotEntries.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const IndexMarketDataSnapshotEntries.encode 10 IndexMarketDataSnapshotEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : IndexMarketDataSnapshotExtensionFields) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 IndexMarketDataSnapshotEntries.encode IndexMarketDataSnapshotEntries.decode IndexMarketDataSnapshotEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.indexMarketDataSnapshotEntries.length_lt]
  rfl

end IndexMarketDataSnapshotExtensionFields

/-- Market Data Snapshot Entries: 19 bytes -/
structure MarketDataSnapshotEntries where
  marketDataSnapshotEntriesMdentrytype : Alpha 2
  marketDataSnapshotEntriesMdentrypx : BitVec 64
  mdentrysize : BitVec 64
  mdentrypositionno : BitVec 8
  deriving DecidableEq, Repr

namespace MarketDataSnapshotEntries

def encode (message : MarketDataSnapshotEntries) : List UInt8 :=
  Alpha.encode message.marketDataSnapshotEntriesMdentrytype
    ++ (encodeUInt 8 message.marketDataSnapshotEntriesMdentrypx
    ++ (encodeUInt 8 message.mdentrysize
    ++ (encodeUInt 1 message.mdentrypositionno)))

def decode (bytes : List UInt8) : Option (MarketDataSnapshotEntries × List UInt8) := do
  let (marketDataSnapshotEntriesMdentrytype, bytes) ← Alpha.decode 2 bytes
  let (marketDataSnapshotEntriesMdentrypx, bytes) ← decodeUInt 8 bytes
  let (mdentrysize, bytes) ← decodeUInt 8 bytes
  let (mdentrypositionno, bytes) ← decodeUInt 1 bytes
  pure ({ marketDataSnapshotEntriesMdentrytype, marketDataSnapshotEntriesMdentrypx, mdentrysize, mdentrypositionno }, bytes)

@[simp] theorem encode_length (message : MarketDataSnapshotEntries) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MarketDataSnapshotEntries) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketDataSnapshotEntries) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MarketDataSnapshotEntries

/-- Market Data Snapshot Extension Fields -/
structure MarketDataSnapshotExtensionFields where
  marketDataSnapshotEntries : Bounded 2 MarketDataSnapshotEntries
  deriving DecidableEq, Repr

namespace MarketDataSnapshotExtensionFields

def encode (message : MarketDataSnapshotExtensionFields) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.marketDataSnapshotEntries.val.length)
    ++ (encodeMany MarketDataSnapshotEntries.encode message.marketDataSnapshotEntries.val)

def decode (bytes : List UInt8) : Option (MarketDataSnapshotExtensionFields × List UInt8) := do
  let (nomdentries, bytes) ← decodeUInt 2 bytes
  let (marketDataSnapshotEntries_, bytes) ← decodeMany MarketDataSnapshotEntries.decode nomdentries.toNat bytes
  if fits_marketDataSnapshotEntries : marketDataSnapshotEntries_.length < 256 ^ 2 then
    pure ({ marketDataSnapshotEntries := ⟨marketDataSnapshotEntries_, fits_marketDataSnapshotEntries⟩ }, bytes)
  else none

theorem encode_length_pos (message : MarketDataSnapshotExtensionFields) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataSnapshotExtensionFields) : (encode message).length ≤ 1245167 := by
  have bound_marketDataSnapshotEntries := message.marketDataSnapshotEntries.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const MarketDataSnapshotEntries.encode 19 MarketDataSnapshotEntries.encode_length]
  omega

@[simp] theorem decode_encode (message : MarketDataSnapshotExtensionFields) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MarketDataSnapshotEntries.encode MarketDataSnapshotEntries.decode MarketDataSnapshotEntries.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.marketDataSnapshotEntries.length_lt]
  rfl

end MarketDataSnapshotExtensionFields

/-- Any Market Data Snapshot Message ExtendFields, selected by MDStreamID -/
inductive MarketDataSnapshotMessageExtendfields where
  | indexMarketDataSnapshotExtensionFields (message : IndexMarketDataSnapshotExtensionFields) -- "MD001" 0x4D44303031
  | marketDataSnapshotExtensionFields (message : MarketDataSnapshotExtensionFields) -- "MD002" 0x4D44303032
  | marketDataSnapshotExtensionFields331856490547 (message : MarketDataSnapshotExtensionFields) -- "MD003" 0x4D44303033
  | marketDataSnapshotExtensionFields331856490548 (message : MarketDataSnapshotExtensionFields) -- "MD004" 0x4D44303034
  | marketDataSnapshotExtensionFields331856556081 (message : MarketDataSnapshotExtensionFields) -- "MD101" 0x4D44313031
  | marketDataSnapshotExtensionFields331856556082 (message : MarketDataSnapshotExtensionFields) -- "MD102" 0x4D44313032
  | marketDataSnapshotExtensionFields331856687153 (message : MarketDataSnapshotExtensionFields) -- "MD301" 0x4D44333031
  | marketDataSnapshotExtensionFields331856621617 (message : MarketDataSnapshotExtensionFields) -- "MD201" 0x4D44323031
  | marketDataSnapshotExtensionFields331857866801 (message : MarketDataSnapshotExtensionFields) -- "MDE01" 0x4D44453031
  | marketDataSnapshotExtensionFields331856621872 (message : MarketDataSnapshotExtensionFields) -- "MD210" 0x4D44323130
  deriving DecidableEq, Repr

namespace MarketDataSnapshotMessageExtendfields

/-- The MDStreamID each message is sent under -/
def tag : MarketDataSnapshotMessageExtendfields → BitVec 40
  | .indexMarketDataSnapshotExtensionFields _ => 331856490545
  | .marketDataSnapshotExtensionFields _ => 331856490546
  | .marketDataSnapshotExtensionFields331856490547 _ => 331856490547
  | .marketDataSnapshotExtensionFields331856490548 _ => 331856490548
  | .marketDataSnapshotExtensionFields331856556081 _ => 331856556081
  | .marketDataSnapshotExtensionFields331856556082 _ => 331856556082
  | .marketDataSnapshotExtensionFields331856687153 _ => 331856687153
  | .marketDataSnapshotExtensionFields331856621617 _ => 331856621617
  | .marketDataSnapshotExtensionFields331857866801 _ => 331857866801
  | .marketDataSnapshotExtensionFields331856621872 _ => 331856621872

def encode : MarketDataSnapshotMessageExtendfields → List UInt8
  | .indexMarketDataSnapshotExtensionFields message => IndexMarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856490547 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856490548 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856556081 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856556082 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856687153 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856621617 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331857866801 message => MarketDataSnapshotExtensionFields.encode message
  | .marketDataSnapshotExtensionFields331856621872 message => MarketDataSnapshotExtensionFields.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MarketDataSnapshotMessageExtendfields) : (encode message).length ≤ 1245167 := by
  cases message with
  | indexMarketDataSnapshotExtensionFields inner =>
    have bound_inner := IndexMarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856490547 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856490548 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856556081 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856556082 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856687153 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856621617 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331857866801 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega
  | marketDataSnapshotExtensionFields331856621872 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (MarketDataSnapshotMessageExtendfields × List UInt8) :=
  if tag = 331856490545 then (IndexMarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.indexMarketDataSnapshotExtensionFields message, rest)
  else if tag = 331856490546 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields message, rest)
  else if tag = 331856490547 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856490547 message, rest)
  else if tag = 331856490548 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856490548 message, rest)
  else if tag = 331856556081 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856556081 message, rest)
  else if tag = 331856556082 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856556082 message, rest)
  else if tag = 331856687153 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856687153 message, rest)
  else if tag = 331856621617 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856621617 message, rest)
  else if tag = 331857866801 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331857866801 message, rest)
  else if tag = 331856621872 then (MarketDataSnapshotExtensionFields.decode bytes).map fun (message, rest) => (.marketDataSnapshotExtensionFields331856621872 message, rest)
  else none

@[simp] theorem decode_encode (message : MarketDataSnapshotMessageExtendfields) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MarketDataSnapshotMessageExtendfields

/-- Market Data Snapshot Message -/
structure MarketDataSnapshotMessage where
  marketDataSnapshotMessageSecuritytype : BitVec 8
  tradsesmode : BitVec 8
  tradedate : BitVec 32
  lastupdatetime : BitVec 32
  securityid : Alpha 8
  symbol : Alpha 8
  preclosepx : BitVec 64
  totalvolumetraded : BitVec 64
  numtrades : BitVec 64
  marketDataSnapshotMessageTotalvaluetraded : BitVec 64
  tradingphasecode : Alpha 8
  marketDataSnapshotMessageExtendfields : MarketDataSnapshotMessageExtendfields
  deriving DecidableEq, Repr

namespace MarketDataSnapshotMessage

def encode (message : MarketDataSnapshotMessage) : List UInt8 :=
  encodeUInt 1 message.marketDataSnapshotMessageSecuritytype
    ++ (encodeUInt 1 message.tradsesmode
    ++ (encodeUInt 4 message.tradedate
    ++ (encodeUInt 4 message.lastupdatetime
    ++ (encodeUInt 5 (MarketDataSnapshotMessageExtendfields.tag message.marketDataSnapshotMessageExtendfields)
    ++ (Alpha.encode message.securityid
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.preclosepx
    ++ (encodeUInt 8 message.totalvolumetraded
    ++ (encodeUInt 8 message.numtrades
    ++ (encodeUInt 8 message.marketDataSnapshotMessageTotalvaluetraded
    ++ (Alpha.encode message.tradingphasecode
    ++ (MarketDataSnapshotMessageExtendfields.encode message.marketDataSnapshotMessageExtendfields))))))))))))

def decode (bytes : List UInt8) : Option (MarketDataSnapshotMessage × List UInt8) := do
  let (marketDataSnapshotMessageSecuritytype, bytes) ← decodeUInt 1 bytes
  let (tradsesmode, bytes) ← decodeUInt 1 bytes
  let (tradedate, bytes) ← decodeUInt 4 bytes
  let (lastupdatetime, bytes) ← decodeUInt 4 bytes
  let (mdstreamid, bytes) ← decodeUInt 5 bytes
  let (securityid, bytes) ← Alpha.decode 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (preclosepx, bytes) ← decodeUInt 8 bytes
  let (totalvolumetraded, bytes) ← decodeUInt 8 bytes
  let (numtrades, bytes) ← decodeUInt 8 bytes
  let (marketDataSnapshotMessageTotalvaluetraded, bytes) ← decodeUInt 8 bytes
  let (tradingphasecode, bytes) ← Alpha.decode 8 bytes
  let (marketDataSnapshotMessageExtendfields, bytes) ← MarketDataSnapshotMessageExtendfields.decode mdstreamid bytes
  pure ({ marketDataSnapshotMessageSecuritytype, tradsesmode, tradedate, lastupdatetime, securityid, symbol, preclosepx, totalvolumetraded, numtrades, marketDataSnapshotMessageTotalvaluetraded, tradingphasecode, marketDataSnapshotMessageExtendfields }, bytes)

theorem encode_length_pos (message : MarketDataSnapshotMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MarketDataSnapshotMessage) : (encode message).length ≤ 1245238 := by
  unfold encode
  cases message.marketDataSnapshotMessageExtendfields with
  | indexMarketDataSnapshotExtensionFields inner =>
    have bound_inner := IndexMarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856490547 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856490548 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856556081 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856556082 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856687153 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856621617 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331857866801 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega
  | marketDataSnapshotExtensionFields331856621872 inner =>
    have bound_inner := MarketDataSnapshotExtensionFields.encode_length_le inner
    simp only [MarketDataSnapshotMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
    omega

@[simp] theorem decode_encode (message : MarketDataSnapshotMessage) (rest : List UInt8) :
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
  rw [MarketDataSnapshotMessageExtendfields.decode_encode, some_bind]
  rfl

end MarketDataSnapshotMessage

/-- Tick-by-Tick Order Market Data Extension Fields: 139 bytes -/
structure TickbytickOrderMarketDataExtensionFields where
  side : Side
  quoteid : Alpha 18
  memberid : Alpha 12
  tradercode : Alpha 12
  fullamounttrade : BitVec 8
  settltype : BitVec 8
  contractmultiplier : BitVec 32
  expirationdays : BitVec 16
  tickbytickOrderMarketDataExtensionFieldsTotalvaluetraded : BitVec 64
  basketid : Alpha 16
  investorname : Alpha 32
  bidtranstype : BitVec 8
  bidexecinsttype : BitVec 8
  expiredate : BitVec 32
  secondaryorderid : Alpha 18
  minqty : BitVec 64
  deriving DecidableEq, Repr

namespace TickbytickOrderMarketDataExtensionFields

def encode (message : TickbytickOrderMarketDataExtensionFields) : List UInt8 :=
  Side.encode message.side
    ++ (Alpha.encode message.quoteid
    ++ (Alpha.encode message.memberid
    ++ (Alpha.encode message.tradercode
    ++ (encodeUInt 1 message.fullamounttrade
    ++ (encodeUInt 1 message.settltype
    ++ (encodeUInt 4 message.contractmultiplier
    ++ (encodeUInt 2 message.expirationdays
    ++ (encodeUInt 8 message.tickbytickOrderMarketDataExtensionFieldsTotalvaluetraded
    ++ (Alpha.encode message.basketid
    ++ (Alpha.encode message.investorname
    ++ (encodeUInt 1 message.bidtranstype
    ++ (encodeUInt 1 message.bidexecinsttype
    ++ (encodeUInt 4 message.expiredate
    ++ (Alpha.encode message.secondaryorderid
    ++ (encodeUInt 8 message.minqty)))))))))))))))

def decode (bytes : List UInt8) : Option (TickbytickOrderMarketDataExtensionFields × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  let (quoteid, bytes) ← Alpha.decode 18 bytes
  let (memberid, bytes) ← Alpha.decode 12 bytes
  let (tradercode, bytes) ← Alpha.decode 12 bytes
  let (fullamounttrade, bytes) ← decodeUInt 1 bytes
  let (settltype, bytes) ← decodeUInt 1 bytes
  let (contractmultiplier, bytes) ← decodeUInt 4 bytes
  let (expirationdays, bytes) ← decodeUInt 2 bytes
  let (tickbytickOrderMarketDataExtensionFieldsTotalvaluetraded, bytes) ← decodeUInt 8 bytes
  let (basketid, bytes) ← Alpha.decode 16 bytes
  let (investorname, bytes) ← Alpha.decode 32 bytes
  let (bidtranstype, bytes) ← decodeUInt 1 bytes
  let (bidexecinsttype, bytes) ← decodeUInt 1 bytes
  let (expiredate, bytes) ← decodeUInt 4 bytes
  let (secondaryorderid, bytes) ← Alpha.decode 18 bytes
  let (minqty, bytes) ← decodeUInt 8 bytes
  pure ({ side, quoteid, memberid, tradercode, fullamounttrade, settltype, contractmultiplier, expirationdays, tickbytickOrderMarketDataExtensionFieldsTotalvaluetraded, basketid, investorname, bidtranstype, bidexecinsttype, expiredate, secondaryorderid, minqty }, bytes)

@[simp] theorem encode_length (message : TickbytickOrderMarketDataExtensionFields) : (encode message).length = 139 := by
  unfold encode
  simp only [List.length_append, Side.encode_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickbytickOrderMarketDataExtensionFields) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickbytickOrderMarketDataExtensionFields) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickbytickOrderMarketDataExtensionFields

/-- Tick-by-Tick Trade Market Data Extension Fields: 53 bytes -/
structure TickbytickTradeMarketDataExtensionFields where
  bidapplseqnum : Alpha 18
  offerapplseqnum : Alpha 18
  tickbytickTradeMarketDataExtensionFieldsTotalvaluetraded : BitVec 64
  trademethod : BitVec 8
  marginprice : BitVec 64
  deriving DecidableEq, Repr

namespace TickbytickTradeMarketDataExtensionFields

def encode (message : TickbytickTradeMarketDataExtensionFields) : List UInt8 :=
  Alpha.encode message.bidapplseqnum
    ++ (Alpha.encode message.offerapplseqnum
    ++ (encodeUInt 8 message.tickbytickTradeMarketDataExtensionFieldsTotalvaluetraded
    ++ (encodeUInt 1 message.trademethod
    ++ (encodeUInt 8 message.marginprice))))

def decode (bytes : List UInt8) : Option (TickbytickTradeMarketDataExtensionFields × List UInt8) := do
  let (bidapplseqnum, bytes) ← Alpha.decode 18 bytes
  let (offerapplseqnum, bytes) ← Alpha.decode 18 bytes
  let (tickbytickTradeMarketDataExtensionFieldsTotalvaluetraded, bytes) ← decodeUInt 8 bytes
  let (trademethod, bytes) ← decodeUInt 1 bytes
  let (marginprice, bytes) ← decodeUInt 8 bytes
  pure ({ bidapplseqnum, offerapplseqnum, tickbytickTradeMarketDataExtensionFieldsTotalvaluetraded, trademethod, marginprice }, bytes)

@[simp] theorem encode_length (message : TickbytickTradeMarketDataExtensionFields) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TickbytickTradeMarketDataExtensionFields) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickbytickTradeMarketDataExtensionFields) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickbytickTradeMarketDataExtensionFields

/-- Any Tick-by-Tick Market Data Message ExtendFields, selected by MDStreamID -/
inductive TickbytickMarketDataMessageExtendfields where
  | tickbytickOrderMarketDataExtensionFields (message : TickbytickOrderMarketDataExtensionFields) -- "MD211" 0x4D44323131
  | tickbytickOrderMarketDataExtensionFields331856621874 (message : TickbytickOrderMarketDataExtensionFields) -- "MD212" 0x4D44323132
  | tickbytickOrderMarketDataExtensionFields331856621875 (message : TickbytickOrderMarketDataExtensionFields) -- "MD213" 0x4D44323133
  | tickbytickOrderMarketDataExtensionFields331856621876 (message : TickbytickOrderMarketDataExtensionFields) -- "MD214" 0x4D44323134
  | tickbytickOrderMarketDataExtensionFields331856621877 (message : TickbytickOrderMarketDataExtensionFields) -- "MD215" 0x4D44323135
  | tickbytickOrderMarketDataExtensionFields331856621878 (message : TickbytickOrderMarketDataExtensionFields) -- "MD216" 0x4D44323136
  | tickbytickTradeMarketDataExtensionFields (message : TickbytickTradeMarketDataExtensionFields) -- "MD217" 0x4D44323137
  deriving DecidableEq, Repr

namespace TickbytickMarketDataMessageExtendfields

/-- The MDStreamID each message is sent under -/
def tag : TickbytickMarketDataMessageExtendfields → BitVec 40
  | .tickbytickOrderMarketDataExtensionFields _ => 331856621873
  | .tickbytickOrderMarketDataExtensionFields331856621874 _ => 331856621874
  | .tickbytickOrderMarketDataExtensionFields331856621875 _ => 331856621875
  | .tickbytickOrderMarketDataExtensionFields331856621876 _ => 331856621876
  | .tickbytickOrderMarketDataExtensionFields331856621877 _ => 331856621877
  | .tickbytickOrderMarketDataExtensionFields331856621878 _ => 331856621878
  | .tickbytickTradeMarketDataExtensionFields _ => 331856621879

def encode : TickbytickMarketDataMessageExtendfields → List UInt8
  | .tickbytickOrderMarketDataExtensionFields message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickOrderMarketDataExtensionFields331856621874 message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickOrderMarketDataExtensionFields331856621875 message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickOrderMarketDataExtensionFields331856621876 message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickOrderMarketDataExtensionFields331856621877 message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickOrderMarketDataExtensionFields331856621878 message => TickbytickOrderMarketDataExtensionFields.encode message
  | .tickbytickTradeMarketDataExtensionFields message => TickbytickTradeMarketDataExtensionFields.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : TickbytickMarketDataMessageExtendfields) : (encode message).length ≤ 139 := by
  cases message with
  | tickbytickOrderMarketDataExtensionFields inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621874 inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621875 inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621876 inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621877 inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621878 inner =>
    simp only [encode, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickTradeMarketDataExtensionFields inner =>
    simp only [encode, TickbytickTradeMarketDataExtensionFields.encode_length]
    omega

def decode (tag : BitVec 40) (bytes : List UInt8) : Option (TickbytickMarketDataMessageExtendfields × List UInt8) :=
  if tag = 331856621873 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields message, rest)
  else if tag = 331856621874 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields331856621874 message, rest)
  else if tag = 331856621875 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields331856621875 message, rest)
  else if tag = 331856621876 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields331856621876 message, rest)
  else if tag = 331856621877 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields331856621877 message, rest)
  else if tag = 331856621878 then (TickbytickOrderMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickOrderMarketDataExtensionFields331856621878 message, rest)
  else if tag = 331856621879 then (TickbytickTradeMarketDataExtensionFields.decode bytes).map fun (message, rest) => (.tickbytickTradeMarketDataExtensionFields message, rest)
  else none

@[simp] theorem decode_encode (message : TickbytickMarketDataMessageExtendfields) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end TickbytickMarketDataMessageExtendfields

/-- Tick-by-Tick Market Data Message -/
structure TickbytickMarketDataMessage where
  tickbytickMarketDataMessageSecuritytype : BitVec 8
  tickbytickMarketDataMessageChannelno : BitVec 16
  applseqnum : BitVec 64
  securityid : Alpha 8
  transacttime : BitVec 32
  exectype : Exectype
  price : BitVec 64
  orderqty : BitVec 64
  tickbytickMarketDataMessageExtendfields : TickbytickMarketDataMessageExtendfields
  deriving DecidableEq, Repr

namespace TickbytickMarketDataMessage

def encode (message : TickbytickMarketDataMessage) : List UInt8 :=
  encodeUInt 1 message.tickbytickMarketDataMessageSecuritytype
    ++ (encodeUInt 2 message.tickbytickMarketDataMessageChannelno
    ++ (encodeUInt 8 message.applseqnum
    ++ (encodeUInt 5 (TickbytickMarketDataMessageExtendfields.tag message.tickbytickMarketDataMessageExtendfields)
    ++ (Alpha.encode message.securityid
    ++ (encodeUInt 4 message.transacttime
    ++ (Exectype.encode message.exectype
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 8 message.orderqty
    ++ (TickbytickMarketDataMessageExtendfields.encode message.tickbytickMarketDataMessageExtendfields)))))))))

def decode (bytes : List UInt8) : Option (TickbytickMarketDataMessage × List UInt8) := do
  let (tickbytickMarketDataMessageSecuritytype, bytes) ← decodeUInt 1 bytes
  let (tickbytickMarketDataMessageChannelno, bytes) ← decodeUInt 2 bytes
  let (applseqnum, bytes) ← decodeUInt 8 bytes
  let (mdstreamid, bytes) ← decodeUInt 5 bytes
  let (securityid, bytes) ← Alpha.decode 8 bytes
  let (transacttime, bytes) ← decodeUInt 4 bytes
  let (exectype, bytes) ← Exectype.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderqty, bytes) ← decodeUInt 8 bytes
  let (tickbytickMarketDataMessageExtendfields, bytes) ← TickbytickMarketDataMessageExtendfields.decode mdstreamid bytes
  pure ({ tickbytickMarketDataMessageSecuritytype, tickbytickMarketDataMessageChannelno, applseqnum, securityid, transacttime, exectype, price, orderqty, tickbytickMarketDataMessageExtendfields }, bytes)

theorem encode_length_pos (message : TickbytickMarketDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TickbytickMarketDataMessage) : (encode message).length ≤ 184 := by
  unfold encode
  cases message.tickbytickMarketDataMessageExtendfields with
  | tickbytickOrderMarketDataExtensionFields inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621874 inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621875 inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621876 inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621877 inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickOrderMarketDataExtensionFields331856621878 inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickOrderMarketDataExtensionFields.encode_length]
    omega
  | tickbytickTradeMarketDataExtensionFields inner =>
    simp only [TickbytickMarketDataMessageExtendfields.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Exectype.encode_length, TickbytickTradeMarketDataExtensionFields.encode_length]
    omega

@[simp] theorem decode_encode (message : TickbytickMarketDataMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Exectype.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TickbytickMarketDataMessageExtendfields.decode_encode, some_bind]
  rfl

end TickbytickMarketDataMessage

/-- Any Message Body, selected by MsgType -/
inductive MessageBody where
  | logonMessage (message : LogonMessage) -- "S001" 0x53303031
  | logoutMessage (message : LogoutMessage) -- "S002" 0x53303032
  | heartbeatMessage (message : HeartbeatMessage) -- "S003" 0x53303033
  | channelHeartbeat (message : ChannelHeartbeat) -- "P001" 0x50303031
  | retransmissionMessage (message : RetransmissionMessage) -- "P002" 0x50303032
  | marketStatusMessage (message : MarketStatusMessage) -- "M101" 0x4D313031
  | marketDataSnapshotMessage (message : MarketDataSnapshotMessage) -- "M102" 0x4D313032
  | tickbytickMarketDataMessage (message : TickbytickMarketDataMessage) -- "M201" 0x4D323031
  deriving DecidableEq, Repr

namespace MessageBody

/-- The MsgType each message is sent under -/
def tag : MessageBody → BitVec 32
  | .logonMessage _ => 1395666993
  | .logoutMessage _ => 1395666994
  | .heartbeatMessage _ => 1395666995
  | .channelHeartbeat _ => 1345335345
  | .retransmissionMessage _ => 1345335346
  | .marketStatusMessage _ => 1295069233
  | .marketDataSnapshotMessage _ => 1295069234
  | .tickbytickMarketDataMessage _ => 1295134769

def encode : MessageBody → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .channelHeartbeat message => ChannelHeartbeat.encode message
  | .retransmissionMessage message => RetransmissionMessage.encode message
  | .marketStatusMessage message => MarketStatusMessage.encode message
  | .marketDataSnapshotMessage message => MarketDataSnapshotMessage.encode message
  | .tickbytickMarketDataMessage message => TickbytickMarketDataMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 1245238 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | channelHeartbeat inner =>
    simp only [encode, ChannelHeartbeat.encode_length]
    omega
  | retransmissionMessage inner =>
    simp only [encode, RetransmissionMessage.encode_length]
    omega
  | marketStatusMessage inner =>
    simp only [encode, MarketStatusMessage.encode_length]
    omega
  | marketDataSnapshotMessage inner =>
    have bound_inner := MarketDataSnapshotMessage.encode_length_le inner
    simp only [encode]
    omega
  | tickbytickMarketDataMessage inner =>
    have bound_inner := TickbytickMarketDataMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 32) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 1395666993 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 1395666994 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 1395666995 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 1345335345 then (ChannelHeartbeat.decode bytes).map fun (message, rest) => (.channelHeartbeat message, rest)
  else if tag = 1345335346 then (RetransmissionMessage.decode bytes).map fun (message, rest) => (.retransmissionMessage message, rest)
  else if tag = 1295069233 then (MarketStatusMessage.decode bytes).map fun (message, rest) => (.marketStatusMessage message, rest)
  else if tag = 1295069234 then (MarketDataSnapshotMessage.decode bytes).map fun (message, rest) => (.marketDataSnapshotMessage message, rest)
  else if tag = 1295134769 then (TickbytickMarketDataMessage.decode bytes).map fun (message, rest) => (.tickbytickMarketDataMessage message, rest)
  else none

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MessageBody

/-- Standard Trailer: 4 bytes -/
structure StandardTrailer where
  checksum : BitVec 32
  deriving DecidableEq, Repr

namespace StandardTrailer

def encode (message : StandardTrailer) : List UInt8 :=
  encodeUInt 4 message.checksum

def decode (bytes : List UInt8) : Option (StandardTrailer × List UInt8) := do
  let (checksum, bytes) ← decodeUInt 4 bytes
  pure ({ checksum }, bytes)

@[simp] theorem encode_length (message : StandardTrailer) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StandardTrailer) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StandardTrailer) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StandardTrailer

/-- Binary Message -/
structure BinaryMessage where
  sendingtime : BitVec 64
  msgseqnum : BitVec 64
  bodylength : BitVec 32
  messageBody : MessageBody
  standardTrailer : StandardTrailer
  deriving DecidableEq, Repr

namespace BinaryMessage

def encode (message : BinaryMessage) : List UInt8 :=
  encodeUInt 4 (MessageBody.tag message.messageBody)
    ++ (encodeUInt 8 message.sendingtime
    ++ (encodeUInt 8 message.msgseqnum
    ++ (encodeUInt 4 message.bodylength
    ++ (MessageBody.encode message.messageBody
    ++ (StandardTrailer.encode message.standardTrailer)))))

def decode (bytes : List UInt8) : Option (BinaryMessage × List UInt8) := do
  let (msgtype, bytes) ← decodeUInt 4 bytes
  let (sendingtime, bytes) ← decodeUInt 8 bytes
  let (msgseqnum, bytes) ← decodeUInt 8 bytes
  let (bodylength, bytes) ← decodeUInt 4 bytes
  let (messageBody, bytes) ← MessageBody.decode msgtype bytes
  let (standardTrailer, bytes) ← StandardTrailer.decode bytes
  pure ({ sendingtime, msgseqnum, bodylength, messageBody, standardTrailer }, bytes)

theorem encode_length_pos (message : BinaryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BinaryMessage) : (encode message).length ≤ 1245266 := by
  unfold encode
  cases message.messageBody with
  | logonMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, LogonMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, HeartbeatMessage.encode_length]
    omega
  | channelHeartbeat inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, ChannelHeartbeat.encode_length]
    omega
  | retransmissionMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, RetransmissionMessage.encode_length]
    omega
  | marketStatusMessage inner =>
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length, MarketStatusMessage.encode_length]
    omega
  | marketDataSnapshotMessage inner =>
    have bound_inner := MarketDataSnapshotMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length]
    omega
  | tickbytickMarketDataMessage inner =>
    have bound_inner := TickbytickMarketDataMessage.encode_length_le inner
    simp only [MessageBody.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StandardTrailer.encode_length]
    omega

@[simp] theorem decode_encode (message : BinaryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MessageBody.decode_encode, some_bind]
  dsimp only
  rw [StandardTrailer.decode_encode, some_bind]
  rfl

end BinaryMessage

/-- Packet -/
structure Packet where
  binaryMessage : List BinaryMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany BinaryMessage.encode message.binaryMessage

def decode (bytes : List UInt8) : Option Packet := do
  let binaryMessage ← decodeAll BinaryMessage.decode bytes.length bytes
  pure { binaryMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany BinaryMessage.encode BinaryMessage.decode BinaryMessage.decode_encode BinaryMessage.encode_length_pos message.binaryMessage _ (encodeMany_length_ge BinaryMessage.encode BinaryMessage.encode_length_pos message.binaryMessage), some_bind]
  rfl

end Packet

end Omi.SseSsesecuritiesMdgwIs120V063
