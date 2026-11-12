/-!
# Wire bytes

The field kinds the definitions are built from, each with an encoder, a decoder, and the lemmas
every message proof leans on: an encoding is as wide as its field says, and decoding what was
encoded gives the value back and leaves the following bytes alone.

Bytes are `List UInt8` rather than `ByteArray`: lists are what the proofs can take apart, and a
`ByteArray` converts at the edges.
-/

namespace Omi

/-- Big-endian bytes of the low `n` bytes of a natural number, most significant first -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => beBytes n (v / 256) ++ [UInt8.ofNat (v % 256)]

/-- The natural number big-endian bytes spell -/
def beValue (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

theorem beBytes_length (n v : Nat) : (beBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem beValue_append_byte (bytes : List UInt8) (byte : UInt8) :
    beValue (bytes ++ [byte]) = beValue bytes * 256 + byte.toNat := by
  simp [beValue, List.foldl_append]

/-- Big-endian bytes read back as the number, reduced to the width they hold -/
theorem beValue_beBytes (n v : Nat) : beValue (beBytes n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [beBytes, beValue, Nat.mod_one]
  | succ n ih =>
    have byte : (UInt8.ofNat (v % 256)).toNat = v % 256 := by simp
    rw [beBytes, beValue_append_byte, ih, byte]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    omega

/-- Split off the first `n` bytes, when there are that many -/
def take? (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

/-- Taking exactly the bytes in front splits them from what follows. The width is a hypothesis rather
    than `front.length` itself, so a caller whose width is a type index never has to rewrite it -/
theorem take?_append {front rest : List UInt8} {n : Nat} (width : front.length = n) :
    take? n (front ++ rest) = some (front, rest) := by
  subst width
  simp [take?]

/-! ## Integers -/

/-- An unsigned big-endian integer `n` bytes wide; a signed field reads the same bits -/
def encodeUInt (n : Nat) (value : BitVec (8 * n)) : List UInt8 :=
  beBytes n value.toNat

def decodeUInt (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n) × List UInt8) :=
  (take? n bytes).map fun (front, rest) => (BitVec.ofNat (8 * n) (beValue front), rest)

@[simp] theorem encodeUInt_length (n : Nat) (value : BitVec (8 * n)) : (encodeUInt n value).length = n :=
  beBytes_length n value.toNat

theorem encodeUInt_length_pos (n : Nat) (pos : 0 < n) (value : BitVec (8 * n)) : (encodeUInt n value).length > 0 := by
  rw [encodeUInt_length]; omega

theorem BitVec.toNat_lt_pow (n : Nat) (value : BitVec (8 * n)) : value.toNat < 256 ^ n := by
  have := value.isLt
  rwa [Nat.pow_mul] at this

@[simp] theorem decodeUInt_encodeUInt (n : Nat) (value : BitVec (8 * n)) (rest : List UInt8) :
    decodeUInt n (encodeUInt n value ++ rest) = some (value, rest) := by
  unfold decodeUInt
  rw [take?_append (encodeUInt_length n value)]
  simp [encodeUInt, beValue_beBytes, Nat.mod_eq_of_lt (BitVec.toNat_lt_pow n value)]

/-- A little-endian integer: the big-endian bytes reversed -/
def encodeUIntLE (n : Nat) (value : BitVec (8 * n)) : List UInt8 :=
  (beBytes n value.toNat).reverse

def decodeUIntLE (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n) × List UInt8) :=
  (take? n bytes).map fun (front, rest) => (BitVec.ofNat (8 * n) (beValue front.reverse), rest)

@[simp] theorem encodeUIntLE_length (n : Nat) (value : BitVec (8 * n)) : (encodeUIntLE n value).length = n := by
  simp [encodeUIntLE, beBytes_length]

theorem encodeUIntLE_length_pos (n : Nat) (pos : 0 < n) (value : BitVec (8 * n)) : (encodeUIntLE n value).length > 0 := by
  rw [encodeUIntLE_length]; omega

@[simp] theorem decodeUIntLE_encodeUIntLE (n : Nat) (value : BitVec (8 * n)) (rest : List UInt8) :
    decodeUIntLE n (encodeUIntLE n value ++ rest) = some (value, rest) := by
  unfold decodeUIntLE
  rw [take?_append (encodeUIntLE_length n value)]
  simp [encodeUIntLE, beValue_beBytes, Nat.mod_eq_of_lt (BitVec.toNat_lt_pow n value)]

/-! ## Text -/

/-- Fixed-width ascii text, exactly as sent: padding is kept, so what is decoded encodes back unchanged -/
structure Alpha (n : Nat) where
  bytes : List UInt8
  length : bytes.length = n
  deriving DecidableEq

instance : Repr (Alpha n) where
  reprPrec alpha _ := repr (String.ofList (alpha.bytes.map fun byte => Char.ofNat byte.toNat))

def Alpha.encode (alpha : Alpha n) : List UInt8 :=
  alpha.bytes

def Alpha.decode (n : Nat) (bytes : List UInt8) : Option (Alpha n × List UInt8) :=
  if h : n ≤ bytes.length then
    some (⟨bytes.take n, by simp [List.length_take]; omega⟩, bytes.drop n)
  else
    none

@[simp] theorem Alpha.encode_length (alpha : Alpha n) : (Alpha.encode alpha).length = n :=
  alpha.length

@[simp] theorem Alpha.decode_encode (alpha : Alpha n) (rest : List UInt8) :
    Alpha.decode n (Alpha.encode alpha ++ rest) = some (alpha, rest) := by
  obtain ⟨bytes, length⟩ := alpha
  subst length
  simp [Alpha.decode, Alpha.encode]

/-! ## Repetition -/

/-- A counted run of items, each decoded by `item` -/
def decodeMany (item : List UInt8 → Option (α × List UInt8)) : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
    let (first, bytes) ← item bytes
    let (others, bytes) ← decodeMany item n bytes
    pure (first :: others, bytes)

/-- Items each encoded by `encode`, back to back -/
def encodeMany (encode : α → List UInt8) (items : List α) : List UInt8 :=
  items.flatMap encode

/-- A counted run decodes back to its items when each item does -/
theorem decodeMany_encodeMany (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : List α) (rest : List UInt8) :
    decodeMany decode items.length (encodeMany encode items ++ rest) = some (items, rest) := by
  induction items with
  | nil => simp [decodeMany, encodeMany]
  | cons first others ih =>
    simp only [encodeMany] at ih ⊢
    simp [decodeMany, List.append_assoc, roundtrip, ih]

/-- A run of constant width items is as long as the count says -/
theorem encodeMany_length_const (encode : α → List UInt8) (width : Nat)
    (fixed : ∀ item, (encode item).length = width) (items : List α) :
    (encodeMany encode items).length = items.length * width := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, fixed, List.length_cons]
    simp only [encodeMany] at ih
    rw [ih, Nat.succ_mul, Nat.add_comm]

/-- A run of non-empty items has at least one byte per item -/
theorem encodeMany_length_ge (encode : α → List UInt8) (nonempty : ∀ item, (encode item).length > 0)
    (items : List α) : items.length ≤ (encodeMany encode items).length := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [encodeMany] at ih
    have := nonempty first
    omega

/-- The length of a list of items each at most `most` bytes -/
theorem encodeMany_length_le (encode : α → List UInt8) (most : Nat)
    (bounded : ∀ item, (encode item).length ≤ most) (items : List α) :
    (encodeMany encode items).length ≤ most * items.length := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [encodeMany] at ih
    have := bounded first
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- One byte of variable length data: the item of a list sized by a length field -/
def Byte.encode (byte : UInt8) : List UInt8 :=
  [byte]

def Byte.decode : List UInt8 → Option (UInt8 × List UInt8)
  | byte :: rest => some (byte, rest)
  | [] => none

@[simp] theorem Byte.encode_length (byte : UInt8) : (Byte.encode byte).length = 1 :=
  rfl

theorem Byte.encode_length_pos (byte : UInt8) : (Byte.encode byte).length > 0 := by
  rw [Byte.encode_length]
  decide

@[simp] theorem Byte.decode_encode (byte : UInt8) (rest : List UInt8) :
    Byte.decode (Byte.encode byte ++ rest) = some (byte, rest) :=
  rfl

/-- Bytes closed by a terminator, which they may not themselves hold -/
abbrev Terminated (terminator : UInt8) := { bytes : List UInt8 // terminator ∉ bytes }

instance {terminator : UInt8} : DecidableEq (Terminated terminator) :=
  inferInstanceAs (DecidableEq { bytes : List UInt8 // terminator ∉ bytes })

instance {terminator : UInt8} : Repr (Terminated terminator) where
  reprPrec terminated precedence := reprPrec terminated.val precedence

/-- The bytes, then the terminator that closes them -/
def encodeTerminated (terminator : UInt8) (item : Terminated terminator) : List UInt8 :=
  item.val ++ [terminator]

/-- The bytes ahead of the first terminator, and what follows it; nothing when none closes them -/
def takeTerminated (terminator : UInt8) : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | byte :: rest =>
    if byte = terminator then some ([], rest)
    else (takeTerminated terminator rest).map fun (taken, left) => (byte :: taken, left)

def decodeTerminated (terminator : UInt8) (bytes : List UInt8) : Option (Terminated terminator × List UInt8) :=
  (takeTerminated terminator bytes).bind fun (taken, rest) =>
    if free : terminator ∉ taken then some (⟨taken, free⟩, rest) else none

/-- Bytes holding no terminator are taken whole, up to the one written after them -/
theorem takeTerminated_append (terminator : UInt8) (bytes : List UInt8) (free : terminator ∉ bytes) (rest : List UInt8) :
    takeTerminated terminator (bytes ++ terminator :: rest) = some (bytes, rest) := by
  induction bytes with
  | nil => simp [takeTerminated]
  | cons byte others ih =>
    have head : byte ≠ terminator := by
      intro same
      exact free (by simp [same])
    have others_free : terminator ∉ others := by
      intro inside
      exact free (by simp [inside])
    simp [takeTerminated, head, ih others_free]

theorem encodeTerminated_length_pos (terminator : UInt8) (item : Terminated terminator) :
    (encodeTerminated terminator item).length > 0 := by
  simp [encodeTerminated]

theorem decodeTerminated_encodeTerminated (terminator : UInt8) (item : Terminated terminator) (rest : List UInt8) :
    decodeTerminated terminator (encodeTerminated terminator item ++ rest) = some (item, rest) := by
  unfold decodeTerminated encodeTerminated
  rw [List.append_assoc, List.cons_append, List.nil_append,
    takeTerminated_append terminator item.val item.property rest]
  simp [item.property]

/-- The bits a value's presence states: the mask when the value is there, nothing when it is not.

    A presence bit set is written from the fields its bits state rather than carried, as a count
    is written from the list it counts, so a set and the fields behind it cannot disagree. -/
def presence {n : Nat} (mask : BitVec n) (present : Bool) : BitVec n :=
  bif present then mask else 0

/-- A value written only when it is there -/
def encodeOptional {α : Type} (encode : α → List UInt8) : Option α → List UInt8
  | none => []
  | some value => encode value

/-- A value read only when the bit stating its presence says it is there -/
def decodeOptional {α : Type} (decode : List UInt8 → Option (α × List UInt8)) (present : Bool)
    (bytes : List UInt8) : Option (Option α × List UInt8) :=
  bif present then (decode bytes).map (fun (value, rest) => (some value, rest))
  else some (none, bytes)

theorem decodeOptional_encodeOptional {α : Type} (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (round : ∀ (value : α) (rest : List UInt8), decode (encode value ++ rest) = some (value, rest))
    (value : Option α) (rest : List UInt8) :
    decodeOptional decode value.isSome (encodeOptional encode value ++ rest) = some (value, rest) := by
  cases value <;> simp [encodeOptional, decodeOptional, round]

/-- The data split a fixed number of bytes from its end: what leads the trailer, and the trailer.

    A field reading to the end of the data reads all of it, so a field behind it can be told
    apart only by counting back from the end, which is sound while every one of them has a fixed
    width. SoupTcp closes each packet with a line feed behind a payload that carries no length,
    so the payload is the packet's data less that one byte. -/
def splitTrailer (width : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bytes.length < width then none
  else some (bytes.take (bytes.length - width), bytes.drop (bytes.length - width))

/-- The trailer is handed on as a stream with nothing after it, so the fields read from it read
    as they do anywhere else: each leads what follows -/
theorem splitTrailer_append (width : Nat) (leading trailer : List UInt8) (fixed : trailer.length = width) :
    splitTrailer width (leading ++ trailer) = some (leading, trailer ++ []) := by
  subst fixed
  simp [splitTrailer]

/-- The ascii digit of a value under ten -/
def digit (value : Nat) : UInt8 := UInt8.ofNat (0x30 + value % 10)

/-- A value written as `n` ascii digits, most significant first, zero filled -/
def encodeDigits : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, value => digit (value / 10 ^ n) :: encodeDigits n (value % 10 ^ n)

/-- The value `n` ascii digits hold, and what follows them; nothing when a byte is no digit -/
def decodeDigits : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bytes => some (0, bytes)
  | _ + 1, [] => none
  | n + 1, byte :: rest =>
    if _digits : 0x30 ≤ byte.toNat ∧ byte.toNat ≤ 0x39
    then (decodeDigits n rest).map fun (value, left) => ((byte.toNat - 0x30) * 10 ^ n + value, left)
    else none

@[simp] theorem encodeDigits_length (n value : Nat) : (encodeDigits n value).length = n := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih => simp [encodeDigits, ih]

/-- The byte an ascii digit is written as -/
theorem digit_toNat (value : Nat) (small : value < 10) : (digit value).toNat = 0x30 + value := by
  unfold digit
  rw [Nat.mod_eq_of_lt small]
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt (show 0x30 + value < 256 by omega)]

/-- Digits written from a value under their limit read that value back -/
theorem decodeDigits_encodeDigits (n value : Nat) (fits : value < 10 ^ n) (rest : List UInt8) :
    decodeDigits n (encodeDigits n value ++ rest) = some (value, rest) := by
  induction n generalizing value with
  | zero =>
    have : value = 0 := by simpa using fits
    simp [encodeDigits, decodeDigits, this]
  | succ n ih =>
    have positive : 0 < 10 ^ n := Nat.pow_pos (by decide)
    have head : value / 10 ^ n < 10 := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact fits)
    have split : value / 10 ^ n * 10 ^ n + value % 10 ^ n = value := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod value (10 ^ n)
    have left : value % 10 ^ n < 10 ^ n := Nat.mod_lt _ positive
    simp only [encodeDigits, List.cons_append, decodeDigits]
    -- the digit and what follows it are taken as they stand, so each reads back by its own value
    generalize value / 10 ^ n = first at head split ⊢
    generalize value % 10 ^ n = others at left split ⊢
    have spelled := digit_toNat first head
    rw [dite_eq_left (show 0x30 ≤ _ ∧ _ ≤ 0x39 from by omega), ih others left]
    simp only [Option.map_some, spelled]
    rw [show 0x30 + first - 0x30 = first from by omega, split]

/-- A list whose length fits `n` ascii digits, so a count written from it as digits needs no
    side condition. Reducible, so a proof may see through it to the list and its bound -/
abbrev Digited (n : Nat) (α : Type) := { items : List α // items.length < 10 ^ n }

instance [DecidableEq α] : DecidableEq (Digited n α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length < 10 ^ n })

instance [Repr α] : Repr (Digited n α) where
  reprPrec digited precedence := reprPrec digited.val precedence

theorem Digited.length_lt (digited : Digited n α) : digited.val.length < 10 ^ n :=
  digited.property

/-- A list whose length fits an `n` byte count, so a count written from it needs no side condition.
    Reducible, so a proof may see through it to the list and its bound -/
abbrev Bounded (n : Nat) (α : Type) := { items : List α // items.length < 256 ^ n }

instance [DecidableEq α] : DecidableEq (Bounded n α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length < 256 ^ n })

instance [Repr α] : Repr (Bounded n α) where
  reprPrec bounded precedence := reprPrec bounded.val precedence

theorem Bounded.length_lt (bounded : Bounded n α) : bounded.val.length < 256 ^ n :=
  bounded.property

/-- Rebuilding a bounded list from its items and any proof gives the list back -/
@[simp] theorem Bounded.mk_val (bounded : Bounded n α) (fits : bounded.val.length < 256 ^ n) :
    (⟨bounded.val, fits⟩ : Bounded n α) = bounded :=
  rfl

/-- A packed field some of whose bits are written from what follows it: the rest is carried, and
    those bits are clear in what is carried, so the two can be put back together -/
abbrev Masked (n : Nat) (mask : BitVec n) := { value : BitVec n // value &&& mask = 0 }

instance {n : Nat} {mask : BitVec n} : DecidableEq (Masked n mask) :=
  inferInstanceAs (DecidableEq { value : BitVec n // value &&& mask = 0 })

instance {n : Nat} {mask : BitVec n} : Repr (Masked n mask) where
  reprPrec masked precedence := reprPrec masked.val precedence

theorem Masked.clear {n : Nat} {mask : BitVec n} (masked : Masked n mask) : masked.val &&& mask = 0 :=
  masked.property

/-- A list whose encodings together fit under an `n` byte length, so a length written from them
    needs no side condition: entries filling the bytes a length field states -/
abbrev Sized (n : Nat) (encode : α → List UInt8) := { items : List α // (encodeMany encode items).length < 256 ^ n }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Sized n encode) :=
  inferInstanceAs (DecidableEq { items : List α // (encodeMany encode items).length < 256 ^ n })

instance [Repr α] {encode : α → List UInt8} : Repr (Sized n encode) where
  reprPrec sized precedence := reprPrec sized.val precedence

theorem Sized.length_lt {encode : α → List UInt8} (sized : Sized n encode) : (encodeMany encode sized.val).length < 256 ^ n :=
  sized.property

/-- A list of exactly `n` items: a group the protocol repeats a fixed number of times -/
abbrev Exact (n : Nat) (α : Type) := { items : List α // items.length = n }

instance [DecidableEq α] : DecidableEq (Exact n α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length = n })

instance [Repr α] : Repr (Exact n α) where
  reprPrec exact precedence := reprPrec exact.val precedence

theorem Exact.length_eq (exact : Exact n α) : exact.val.length = n :=
  exact.property

/-- A fixed count reads an exact list back: the decoder reads as many items as the list holds -/
theorem decodeMany_exact (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : Exact n α) (rest : List UInt8) :
    decodeMany decode n (encodeMany encode items.val ++ rest) = some (items.val, rest) := by
  have counted := decodeMany_encodeMany encode decode roundtrip items.val rest
  rw [items.length_eq] at counted
  exact counted

/-- Binding a known value feeds it straight on: the one step a decoder's round trip takes per field.
    Stated on the monadic bind the do notation produces, so no pass over the decoder is needed first -/
theorem some_bind (a : α) (f : α → Option β) : (some a >>= f) = f a :=
  rfl

/-- Bytes to the end of a frame, at most `most` of them, so the frame's length prefix always fits -/
abbrev Capped (most : Nat) := { bytes : List UInt8 // bytes.length ≤ most }

theorem Capped.length_le (capped : Capped most) : capped.val.length ≤ most :=
  capped.property

/-- A count written from a bounded list reads that list back: the count fits its bytes, so the
    decoder reads exactly as many items as were written -/
theorem decodeMany_bounded (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : Bounded n α) (rest : List UInt8) :
    decodeMany decode (BitVec.ofNat (8 * n) items.val.length).toNat (encodeMany encode items.val ++ rest)
      = some (items.val, rest) := by
  have fits : items.val.length < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact items.length_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, decodeMany_encodeMany encode decode roundtrip]

/-- A list whose length the prefix states with a constant added: the prefix counts the list and that
    much besides, so the list is what the prefix states less the constant, and what must fit the
    prefix is the pair of them. Nyse's options gateway states its sequenced message as the message
    length less four, the four being the header the length also counts -/
abbrev Counting (n offset : Nat) (α : Type) := { items : List α // items.length + offset < 256 ^ n }

instance [DecidableEq α] : DecidableEq (Counting n offset α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length + offset < 256 ^ n })

instance [Repr α] : Repr (Counting n offset α) where
  reprPrec counting precedence := reprPrec counting.val precedence

theorem Counting.length_lt (counting : Counting n offset α) : counting.val.length + offset < 256 ^ n :=
  counting.property

@[simp] theorem Counting.mk_val (counting : Counting n offset α) (fits : counting.val.length + offset < 256 ^ n) :
    (⟨counting.val, fits⟩ : Counting n offset α) = counting :=
  rfl

/-- Read back by the prefix less the constant, which is the length the prefix was written from -/
theorem decodeMany_counting (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : Counting n offset α) (rest : List UInt8) :
    decodeMany decode ((BitVec.ofNat (8 * n) (items.val.length + offset)).toNat - offset) (encodeMany encode items.val ++ rest)
      = some (items.val, rest) := by
  have fits : items.val.length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact items.length_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Nat.add_sub_cancel,
    decodeMany_encodeMany encode decode roundtrip]

/-- Items decoded until the bytes run out, each decoder call handed at most `fuel` more turns -/
def decodeAll (item : List UInt8 → Option (α × List UInt8)) : Nat → List UInt8 → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bytes => do
    let (first, rest) ← item bytes
    let others ← decodeAll item fuel rest
    pure (first :: others)

/-- Every item is at least a byte, so a run of items decodes back with fuel to spare -/
theorem decodeAll_encodeMany (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (items : List α) (fuel : Nat) (enough : items.length ≤ fuel) :
    decodeAll decode fuel (encodeMany encode items) = some items := by
  induction items generalizing fuel with
  | nil => cases fuel <;> simp [decodeAll, encodeMany]
  | cons first others ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [encodeMany, List.flatMap_cons]
      have long : (encode first ++ List.flatMap encode others).length > 0 := by
        rw [List.length_append]
        have := nonempty first
        omega
      obtain ⟨byte, tail, spelled⟩ : ∃ byte tail, encode first ++ List.flatMap encode others = byte :: tail := by
        cases h : encode first ++ List.flatMap encode others with
        | nil => rw [h] at long; simp at long
        | cons byte tail => exact ⟨byte, tail, rfl⟩
      rw [spelled]
      have step := roundtrip first (List.flatMap encode others)
      rw [spelled] at step
      have more := ih fuel (by simpa using enough)
      simp only [encodeMany] at more
      simp [decodeAll, step, more]

/-- Items read from the next `size` bytes, to the end of them, and what follows those bytes -/
def decodeSized (item : List UInt8 → Option (α × List UInt8)) (size : Nat) (bytes : List UInt8) : Option (List α × List UInt8) :=
  if size ≤ bytes.length then do
    let items ← decodeAll item size (bytes.take size)
    pure (items, bytes.drop size)
  else none

/-- Items written back to back under a length holding their bytes read back, with what followed -/
theorem decodeSized_encodeMany (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (items : Sized n encode) (rest : List UInt8) :
    decodeSized decode (BitVec.ofNat (8 * n) (encodeMany encode items.val).length).toNat (encodeMany encode items.val ++ rest)
      = some (items.val, rest) := by
  have fits : (encodeMany encode items.val).length < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact items.length_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  unfold decodeSized
  rw [List.take_left, List.drop_left,
    decodeAll_encodeMany encode decode roundtrip nonempty items.val _ (encodeMany_length_ge encode nonempty items.val)]
  simp [List.length_append]

/-- What may close a message: written when there, nothing when not -/
def encodeTail (encode : α → List UInt8) : Option α → List UInt8
  | none => []
  | some item => encode item

/-- What may close a message: read when bytes remain and must take them all, absent when none do -/
def decodeTail (read : List UInt8 → Option (α × List UInt8)) : List UInt8 → Option (Option α)
  | [] => some none
  | bytes => (read bytes).bind fun (item, rest) => if rest.isEmpty then some (some item) else none

/-- A closing item written back, or nothing, reads back as it was -/
theorem decodeTail_encodeTail (encode : α → List UInt8) (read : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, read (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (tail : Option α) :
    decodeTail read (encodeTail encode tail) = some tail := by
  cases tail with
  | none => rfl
  | some item =>
    have long := nonempty item
    obtain ⟨byte, rest, spelled⟩ : ∃ byte rest, encode item = byte :: rest := by
      cases h : encode item with
      | nil => rw [h] at long; simp at long
      | cons byte rest => exact ⟨byte, rest, rfl⟩
    have step := roundtrip item []
    rw [List.append_nil, spelled] at step
    simp [encodeTail, spelled, decodeTail, step]

/-- A field present only while bytes remain: read when the body still has bytes, taking all of
    them, and absent when none do. The body that holds it is read whole within its frame, so what
    is left after the fixed fields ahead of it is exactly this field or nothing — which is what an
    optional rule stating presence on the remaining bytes means. It is written with encodeOptional,
    the value when there and nothing when not. -/
def decodeRemaining {α : Type} (decode : List UInt8 → Option (α × List UInt8)) : List UInt8 → Option (Option α)
  | [] => some none
  | bytes => (decode bytes).bind fun (value, rest) => if rest.isEmpty then some (some value) else none

/-- A closing optional field written back, or nothing, reads back as it was -/
theorem decodeRemaining_encodeOptional {α : Type} (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ value rest, decode (encode value ++ rest) = some (value, rest))
    (nonempty : ∀ value, (encode value).length > 0)
    (value : Option α) :
    decodeRemaining decode (encodeOptional encode value) = some value := by
  cases value with
  | none => rfl
  | some item =>
    have long := nonempty item
    obtain ⟨byte, rest, spelled⟩ : ∃ byte rest, encode item = byte :: rest := by
      cases h : encode item with
      | nil => rw [h] at long; simp at long
      | cons byte rest => exact ⟨byte, rest, rfl⟩
    have step := roundtrip item []
    rw [List.append_nil, spelled] at step
    simp [encodeOptional, spelled, decodeRemaining, step]

/-- A body present only while bytes remain, where the body reads the whole of what it is given:
    a dispatch whose messages close the frame is read that way, so there is no remainder to ask
    about — the bytes are the body or there are none. Written with encodeOptional, as any closing
    optional is. -/
def decodeRemainingAll {α : Type} (decode : List UInt8 → Option α) : List UInt8 → Option (Option α)
  | [] => some none
  | bytes => (decode bytes).map some

/-- A closing optional read whole, written back, reads back as it was -/
theorem decodeRemainingAll_encodeOptional {α : Type} (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (nonempty : ∀ value, (encode value).length > 0)
    (value : Option α) :
    decodeRemainingAll decode (encodeOptional encode value) = some value := by
  cases value with
  | none => rfl
  | some item =>
    have long := nonempty item
    obtain ⟨byte, rest, spelled⟩ : ∃ byte rest, encode item = byte :: rest := by
      cases h : encode item with
      | nil => rw [h] at long; simp at long
      | cons byte rest => exact ⟨byte, rest, rfl⟩
    have step := roundtrip item
    rw [spelled] at step
    simp [encodeOptional, spelled, decodeRemainingAll, step]

/-! ## Framing -/

/-- A length prefix of `n` big endian bytes holding the body's length plus `offset`, then the body.
    The round trip lemmas take their facts at the one message framed, so a body decoder handed the
    fields read ahead of the prefix (a protocol id, flags) qualifies: it need only read back that
    message, not every message -/
def encodeFramed (n offset : Nat) (encode : α → List UInt8) (item : α) : List UInt8 :=
  encodeUInt n (BitVec.ofNat (8 * n) ((encode item).length + offset)) ++ encode item

/-- Read the prefix, take the bytes it counts, and decode them as one whole body -/
def decodeFramed (n offset : Nat) (decode : List UInt8 → Option (α × List UInt8)) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUInt n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let (item, tail) ← decode body
  guard tail.isEmpty
  pure (item, rest)

theorem decodeFramed_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : α)
    (roundtrip : ∀ rest, decode (encode item ++ rest) = some (item, rest))
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramed n offset decode (encodeFramed n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  have whole := roundtrip []
  rw [List.append_nil] at whole
  unfold decodeFramed encodeFramed
  rw [List.append_assoc, decodeUInt_encodeUInt]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole, guard]

theorem encodeFramed_length (n offset : Nat) (encode : α → List UInt8) (item : α) :
    (encodeFramed n offset encode item).length = n + (encode item).length := by
  simp [encodeFramed]

/-- The little endian frame: the same prefix, low byte first -/
def encodeFramedLE (n offset : Nat) (encode : α → List UInt8) (item : α) : List UInt8 :=
  encodeUIntLE n (BitVec.ofNat (8 * n) ((encode item).length + offset)) ++ encode item

def decodeFramedLE (n offset : Nat) (decode : List UInt8 → Option (α × List UInt8)) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUIntLE n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let (item, tail) ← decode body
  guard tail.isEmpty
  pure (item, rest)

theorem decodeFramedLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : α)
    (roundtrip : ∀ rest, decode (encode item ++ rest) = some (item, rest))
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedLE n offset decode (encodeFramedLE n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  have whole := roundtrip []
  rw [List.append_nil] at whole
  unfold decodeFramedLE encodeFramedLE
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole, guard]

theorem encodeFramedLE_length (n offset : Nat) (encode : α → List UInt8) (item : α) :
    (encodeFramedLE n offset encode item).length = n + (encode item).length := by
  simp [encodeFramedLE]

/-- Read the prefix, take the bytes it counts, and decode them as a body that runs to their end -/
def decodeFramedAll (n offset : Nat) (decode : List UInt8 → Option α) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUInt n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let item ← decode body
  pure (item, rest)

theorem decodeFramedAll_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : α)
    (whole : decode (encode item) = some item)
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedAll n offset decode (encodeFramed n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  unfold decodeFramedAll encodeFramed
  rw [List.append_assoc, decodeUInt_encodeUInt]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole]

def decodeFramedAllLE (n offset : Nat) (decode : List UInt8 → Option α) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUIntLE n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let item ← decode body
  pure (item, rest)

theorem decodeFramedAllLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : α)
    (whole : decode (encode item) = some item)
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedAllLE n offset decode (encodeFramedLE n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  unfold decodeFramedAllLE encodeFramedLE
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole]

/-! ## Fitting bodies -/

/-- A body with the proof its encoding fits its frame's length prefix. Where no bound of the fields
    fits the prefix (groups counted in two bytes under a two byte length), every message carries the
    fit instead, and the frame proof uses that -/
abbrev Fitting (encode : α → List UInt8) (offset limit : Nat) := { item : α // (encode item).length + offset < limit }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Fitting encode offset limit) :=
  inferInstanceAs (DecidableEq { item : α // (encode item).length + offset < limit })

instance [Repr α] {encode : α → List UInt8} : Repr (Fitting encode offset limit) where
  reprPrec fitting precedence := reprPrec fitting.val precedence

theorem Fitting.fits {encode : α → List UInt8} (fitting : Fitting encode offset limit) :
    (encode fitting.val).length + offset < limit :=
  fitting.property

/-- Read the frame and its body, and keep the body with the fit the prefix showed -/
def decodeFitting (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramed n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFitting_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : Fitting encode offset (256 ^ n))
    (roundtrip : ∀ rest, decode (encode item.val ++ rest) = some (item.val, rest))
    (rest : List UInt8) :
    decodeFitting n offset encode decode (encodeFramed n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFitting
  rw [decodeFramed_encodeFramed n offset encode decode item.val roundtrip item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

def decodeFittingLE (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedLE n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : Fitting encode offset (256 ^ n))
    (roundtrip : ∀ rest, decode (encode item.val ++ rest) = some (item.val, rest))
    (rest : List UInt8) :
    decodeFittingLE n offset encode decode (encodeFramedLE n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingLE
  rw [decodeFramedLE_encodeFramedLE n offset encode decode item.val roundtrip item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

/-- The same for a body that runs to the end of its frame -/
def decodeFittingAll (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option α)
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedAll n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingAll_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : Fitting encode offset (256 ^ n))
    (whole : decode (encode item.val) = some item.val)
    (rest : List UInt8) :
    decodeFittingAll n offset encode decode (encodeFramed n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingAll
  rw [decodeFramedAll_encodeFramed n offset encode decode item.val whole item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

def decodeFittingAllLE (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option α)
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedAllLE n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingAllLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : Fitting encode offset (256 ^ n))
    (whole : decode (encode item.val) = some item.val)
    (rest : List UInt8) :
    decodeFittingAllLE n offset encode decode (encodeFramedLE n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingAllLE
  rw [decodeFramedAllLE_encodeFramedLE n offset encode decode item.val whole item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

/-! ## Closed bodies -/

/-- A body with the proof its encoding holds no terminator, so the terminator written after it is
    the first and ends it. A stream of such bodies is read one terminator at a time: what a length
    prefix does by counting, a terminator does by closing, and the body carries the proof because no
    bound of the fields can rule the byte out -/
abbrev Closed (encode : α → List UInt8) (terminator : UInt8) := { item : α // terminator ∉ encode item }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Closed encode terminator) :=
  inferInstanceAs (DecidableEq { item : α // terminator ∉ encode item })

instance [Repr α] {encode : α → List UInt8} : Repr (Closed encode terminator) where
  reprPrec closed precedence := reprPrec closed.val precedence

theorem Closed.free {encode : α → List UInt8} (closed : Closed encode terminator) :
    terminator ∉ encode closed.val :=
  closed.property

/-- The body, then the terminator that closes it -/
def encodeClosed (terminator : UInt8) (encode : α → List UInt8) (item : α) : List UInt8 :=
  encode item ++ [terminator]

theorem encodeClosed_length (terminator : UInt8) (encode : α → List UInt8) (item : α) :
    (encodeClosed terminator encode item).length = (encode item).length + 1 := by
  simp [encodeClosed]

theorem encodeClosed_length_pos (terminator : UInt8) (encode : α → List UInt8) (item : α) :
    (encodeClosed terminator encode item).length > 0 := by
  rw [encodeClosed_length]
  omega

/-- Take the bytes up to the terminator and read them as a body that runs to their end -/
def decodeClosedAll (terminator : UInt8) (decode : List UInt8 → Option α) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (body, rest) ← takeTerminated terminator bytes
  let item ← decode body
  pure (item, rest)

theorem decodeClosedAll_encodeClosed (terminator : UInt8) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : α)
    (whole : decode (encode item) = some item)
    (free : terminator ∉ encode item)
    (rest : List UInt8) :
    decodeClosedAll terminator decode (encodeClosed terminator encode item ++ rest) = some (item, rest) := by
  have joined : encodeClosed terminator encode item ++ rest = encode item ++ terminator :: rest := by
    simp [encodeClosed]
  unfold decodeClosedAll
  rw [joined, takeTerminated_append terminator (encode item) free rest, some_bind]
  simp [whole]

/-- The same, keeping the proof the body holds no terminator, which the decoder checks as it reads -/
def decodeClosing (terminator : UInt8) (encode : α → List UInt8) (decode : List UInt8 → Option α)
    (bytes : List UInt8) : Option (Closed encode terminator × List UInt8) := do
  let (item, rest) ← decodeClosedAll terminator decode bytes
  if free : terminator ∉ encode item then pure (⟨item, free⟩, rest) else none

theorem decodeClosing_encodeClosed (terminator : UInt8) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : Closed encode terminator)
    (whole : decode (encode item.val) = some item.val)
    (rest : List UInt8) :
    decodeClosing terminator encode decode (encodeClosed terminator encode item.val ++ rest) = some (item, rest) := by
  unfold decodeClosing
  rw [decodeClosedAll_encodeClosed terminator encode decode item.val whole item.free, some_bind]
  dsimp only
  rw [dite_eq_left item.free]
  rfl

/-! ## Fallbacks -/

/-- A body framed by the very length its choice is keyed on, with the proof that length fits the
    `w` bit key and is none of the values the choice lists: the case the choice falls back to when
    no listed value matches. MoldUdp keys each message block on its length, zero ending the session
    and any other length the bytes of a message -/
abbrev Fallback (encode : α → List UInt8) (w : Nat) (listed : List Nat) :=
  { item : α // (encode item).length < 2 ^ w ∧ (encode item).length ∉ listed }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Fallback encode w listed) :=
  inferInstanceAs (DecidableEq { item : α // (encode item).length < 2 ^ w ∧ (encode item).length ∉ listed })

instance [Repr α] {encode : α → List UInt8} : Repr (Fallback encode w listed) where
  reprPrec fallback precedence := reprPrec fallback.val precedence

/-- The key a fallback is written under: the length of its body -/
def Fallback.key {encode : α → List UInt8} (fallback : Fallback encode w listed) : BitVec w :=
  BitVec.ofNat w (encode fallback.val).length

/-- The key a fallback is written under is none of the values the choice lists -/
theorem Fallback.key_ne {encode : α → List UInt8} (fallback : Fallback encode w listed)
    (code : Nat) (named : code ∈ listed) (small : code < 2 ^ w) :
    fallback.key ≠ BitVec.ofNat w code := by
  intro same
  have spelled := congrArg BitVec.toNat same
  simp only [Fallback.key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fallback.property.1, Nat.mod_eq_of_lt small] at spelled
  exact fallback.property.2 (spelled ▸ named)

/-- Read the bytes the key counts as one whole body, kept with the proof it fits the key and is none
    of the listed values -/
def decodeFallback (w : Nat) (listed : List Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8)) (key : Nat) (bytes : List UInt8) :
    Option (Fallback encode w listed × List UInt8) := do
  let (body, rest) ← take? key bytes
  let (item, tail) ← decode body
  guard tail.isEmpty
  if fits : (encode item).length < 2 ^ w ∧ (encode item).length ∉ listed then pure (⟨item, fits⟩, rest) else none

/-- A fallback read back by its key: the bytes the key counts are its body, and the body is it -/
theorem decodeFallback_encode (w : Nat) (listed : List Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (fallback : Fallback encode w listed)
    (roundtrip : ∀ rest, decode (encode fallback.val ++ rest) = some (fallback.val, rest))
    (rest : List UInt8) :
    decodeFallback w listed encode decode fallback.key.toNat (encode fallback.val ++ rest) = some (fallback, rest) := by
  have whole := roundtrip []
  rw [List.append_nil] at whole
  unfold decodeFallback Fallback.key
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fallback.property.1, take?_append rfl]
  simp only [Bind.bind, Option.bind_some, whole]
  simp [guard, fallback.property]

/-! ## Peeked messages -/

/- A message told apart by a byte inside its own encoding rather than a tag ahead of it: xmt's packet body
    is a heartbeat when the third byte of its first body is the heartbeat's message type, and business
    bodies otherwise, the length that frames each body leading that byte. The byte is read without
    taking it, and each arm carries the proof of what its encoding holds there, so the arm read is the
    arm written -/

/-- A value whose encoding holds `key` at `offset`: the arm a peeked dispatch takes on that key -/
abbrev Keyed (encode : α → List UInt8) (offset : Nat) (key : UInt8) := { item : α // (encode item)[offset]? = some key }

/-- A value whose encoding holds a byte other than `key` at `offset`: the arm a peeked dispatch takes on any other -/
abbrev Unkeyed (encode : α → List UInt8) (offset : Nat) (key : UInt8) := { item : α // ((encode item)[offset]?.any (· ≠ key)) = true }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Keyed encode offset key) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Unkeyed encode offset key) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance [Repr α] {encode : α → List UInt8} : Repr (Keyed encode offset key) where
  reprPrec item prec := reprPrec item.val prec

instance [Repr α] {encode : α → List UInt8} : Repr (Unkeyed encode offset key) where
  reprPrec item prec := reprPrec item.val prec

/-- A message told by the byte at `offset` of its own encoding, read without taking it: `key` there is the keyed arm, any other byte the other -/
abbrev Peeked (α β : Type) (encodeKeyed : α → List UInt8) (encodeOther : β → List UInt8) (offset : Nat) (key : UInt8) :=
  Keyed encodeKeyed offset key ⊕ Unkeyed encodeOther offset key

def decodeKeyed (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8)) (offset : Nat) (key : UInt8)
    (bytes : List UInt8) : Option (Keyed encode offset key × List UInt8) :=
  match decode bytes with
  | some (item, rest) => if keyed : (encode item)[offset]? = some key then some (⟨item, keyed⟩, rest) else none
  | none => none

def decodeUnkeyed (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8)) (offset : Nat) (key : UInt8)
    (bytes : List UInt8) : Option (Unkeyed encode offset key × List UInt8) :=
  match decode bytes with
  | some (item, rest) => if other : ((encode item)[offset]?.any (· ≠ key)) = true then some (⟨item, other⟩, rest) else none
  | none => none

def encodePeek (encodeKeyed : α → List UInt8) (encodeOther : β → List UInt8) :
    Peeked α β encodeKeyed encodeOther offset key → List UInt8
  | .inl item => encodeKeyed item.val
  | .inr item => encodeOther item.val

def decodePeek (offset : Nat) (key : UInt8)
    (keyed : List UInt8 → Option (α × List UInt8)) (other : List UInt8 → Option (β × List UInt8))
    (bytes : List UInt8) : Option ((α ⊕ β) × List UInt8) :=
  if bytes[offset]? = some key then
    match keyed bytes with
    | some (item, rest) => some (.inl item, rest)
    | none => none
  else
    match other bytes with
    | some (item, rest) => some (.inr item, rest)
    | none => none

theorem decodeKeyed_encode (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8)) (offset : Nat) (key : UInt8)
    (roundTrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (item : Keyed encode offset key) (rest : List UInt8) :
    decodeKeyed encode decode offset key (encode item.val ++ rest) = some (item, rest) := by
  unfold decodeKeyed
  rw [roundTrip]
  dsimp only
  rw [dite_eq_left item.property]

theorem decodeUnkeyed_encode (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8)) (offset : Nat) (key : UInt8)
    (roundTrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (item : Unkeyed encode offset key) (rest : List UInt8) :
    decodeUnkeyed encode decode offset key (encode item.val ++ rest) = some (item, rest) := by
  unfold decodeUnkeyed
  rw [roundTrip]
  dsimp only
  rw [dite_eq_left item.property]

/-- The byte at `offset` of a keyed arm's encoding is its key, and something else for the other arm: either way, the offset lies inside the encoding -/
theorem Keyed.within {encode : α → List UInt8} (item : Keyed encode offset key) : offset < (encode item.val).length := by
  have h := item.property
  rw [List.getElem?_eq_some_iff] at h
  exact h.1

theorem Unkeyed.within {encode : α → List UInt8} (item : Unkeyed encode offset key) : offset < (encode item.val).length := by
  have h := item.property
  cases e : (encode item.val)[offset]? with
  | none => rw [e] at h; simp at h
  | some _ => rw [List.getElem?_eq_some_iff] at e; exact e.1

/-- A peeked message decodes to what it was encoded from: the byte its arm holds at the offset is the one the dispatch reads, whatever follows it -/
theorem decodePeek_encodePeek (encodeKeyed : α → List UInt8) (decodeKeyed' : List UInt8 → Option (α × List UInt8))
    (encodeOther : β → List UInt8) (decodeOther : List UInt8 → Option (β × List UInt8)) (offset : Nat) (key : UInt8)
    (keyedTrip : ∀ item rest, decodeKeyed' (encodeKeyed item ++ rest) = some (item, rest))
    (otherTrip : ∀ item rest, decodeOther (encodeOther item ++ rest) = some (item, rest))
    (message : Peeked α β encodeKeyed encodeOther offset key) (rest : List UInt8) :
    decodePeek offset key (decodeKeyed encodeKeyed decodeKeyed' offset key) (decodeUnkeyed encodeOther decodeOther offset key)
      (encodePeek encodeKeyed encodeOther message ++ rest) = some (message, rest) := by
  cases message with
  | inl item =>
    have read : (encodeKeyed item.val ++ rest)[offset]? = some key := by
      rw [List.getElem?_append_left item.within]; exact item.property
    unfold decodePeek encodePeek
    rw [ite_eq_left read, decodeKeyed_encode encodeKeyed decodeKeyed' offset key keyedTrip item rest]
  | inr item =>
    have read : ¬ (encodeOther item.val ++ rest)[offset]? = some key := by
      rw [List.getElem?_append_left item.within]
      intro same
      have h := item.property
      rw [same] at h
      simp at h
    unfold decodePeek encodePeek
    rw [ite_eq_right read, decodeUnkeyed_encode encodeOther decodeOther offset key otherTrip item rest]

/-- A peeked message's encoding is at least a byte: it holds one at the offset -/
theorem encodePeek_length_pos {encodeKeyed : α → List UInt8} {encodeOther : β → List UInt8} {offset : Nat} {key : UInt8}
    (message : Peeked α β encodeKeyed encodeOther offset key) : (encodePeek encodeKeyed encodeOther message).length > 0 := by
  cases message with
  | inl item => exact Nat.lt_of_le_of_lt (Nat.zero_le offset) item.within
  | inr item => exact Nat.lt_of_le_of_lt (Nat.zero_le offset) item.within

/-! ## Fix tag=value fields: a tag, its value, and the separator that ends it -/

/-- The bytes after a known lead, or nothing where they do not start with it -/
def stripPrefix (lead : List UInt8) (bytes : List UInt8) : Option (List UInt8) :=
  if lead.isPrefixOf bytes then some (bytes.drop lead.length) else none

theorem stripPrefix_append (lead rest : List UInt8) : stripPrefix lead (lead ++ rest) = some rest := by
  simp [stripPrefix, List.isPrefixOf_iff_prefix]

/-- A tagged field: its tag, then its value, then the separator that ends it -/
def encodeTagged (tag : List UInt8) (value : Terminated 1) : List UInt8 :=
  tag ++ encodeTerminated 1 value

def decodeTagged (tag : List UInt8) (bytes : List UInt8) : Option (Terminated 1 × List UInt8) :=
  (stripPrefix tag bytes).bind (decodeTerminated 1)

theorem decodeTagged_encodeTagged (tag : List UInt8) (value : Terminated 1) (rest : List UInt8) :
    decodeTagged tag (encodeTagged tag value ++ rest) = some (value, rest) := by
  unfold decodeTagged encodeTagged
  rw [List.append_assoc, stripPrefix_append]
  exact decodeTerminated_encodeTerminated 1 value rest

/-! ## Fix numbers: a count or a length, its decimal digits up to the separator -/

/-- The decimal digits of a number, most significant first, with no leading zero: what a venue writes -/
def encodeDecimal (value : Nat) : List UInt8 :=
  if value < 10 then [UInt8.ofNat (48 + value)] else encodeDecimal (value / 10) ++ [UInt8.ofNat (48 + value % 10)]
termination_by value
decreasing_by omega

/-- The number decimal digits make, or nothing where a byte is not a digit or there are none -/
def decodeDecimal (digits : List UInt8) : Option Nat :=
  if digits.isEmpty then none else
  digits.foldl (fun acc byte => acc.bind fun n => if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (10 * n + (byte.toNat - 48)) else none) (some 0)

theorem encodeDecimal_digits (value : Nat) : ∀ byte ∈ encodeDecimal value, 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 := by
  unfold encodeDecimal
  split
  · intro byte inside
    simp at inside
    subst inside
    simp [UInt8.toNat_ofNat]; omega
  · intro byte inside
    simp only [List.mem_append, List.mem_singleton] at inside
    rcases inside with left | right
    · exact encodeDecimal_digits (value / 10) byte left
    · subst right; simp [UInt8.toNat_ofNat]; omega
termination_by value
decreasing_by omega

theorem encodeDecimal_ne_nil (value : Nat) : encodeDecimal value ≠ [] := by
  unfold encodeDecimal; split <;> simp

theorem foldl_decimalDigits (digits : List UInt8) (start : Nat) (all : ∀ byte ∈ digits, 48 ≤ byte.toNat ∧ byte.toNat ≤ 57) :
    digits.foldl (fun acc byte => acc.bind fun n => if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (10 * n + (byte.toNat - 48)) else none) (some start)
      = some (digits.foldl (fun n byte => 10 * n + (byte.toNat - 48)) start) := by
  induction digits generalizing start with
  | nil => rfl
  | cons byte others ih =>
    have this := all byte (by simp)
    simp only [List.foldl_cons, Option.bind_some, this, and_self, ite_true]
    exact ih _ (fun b inside => all b (by simp [inside]))

theorem foldl_encodeDecimal (value : Nat) : (encodeDecimal value).foldl (fun n byte => 10 * n + (byte.toNat - 48)) 0 = value := by
  unfold encodeDecimal
  split
  · simp [UInt8.toNat_ofNat]; omega
  · rw [List.foldl_append, foldl_encodeDecimal (value / 10)]
    simp [UInt8.toNat_ofNat]; omega
termination_by value
decreasing_by omega

theorem decodeDecimal_encodeDecimal (value : Nat) : decodeDecimal (encodeDecimal value) = some value := by
  unfold decodeDecimal
  rw [ite_eq_right (by simp [encodeDecimal_ne_nil]), foldl_decimalDigits _ 0 (encodeDecimal_digits value), foldl_encodeDecimal]

/-- A number tagged on the wire: its tag, its digits, the separator -/
def encodeTaggedNumber (tag : List UInt8) (value : Nat) : List UInt8 :=
  tag ++ encodeDecimal value ++ [1]

def decodeTaggedNumber (tag : List UInt8) (bytes : List UInt8) : Option (Nat × List UInt8) := do
  let (digits, rest) ← decodeTagged tag bytes
  let value ← decodeDecimal digits.val
  pure (value, rest)

theorem encodeDecimal_free (value : Nat) : (1 : UInt8) ∉ encodeDecimal value := by
  intro inside
  have := encodeDecimal_digits value 1 inside
  simp at this

theorem decodeTaggedNumber_encode (tag : List UInt8) (value : Nat) (rest : List UInt8) :
    decodeTaggedNumber tag (encodeTaggedNumber tag value ++ rest) = some (value, rest) := by
  have as_tagged : encodeTaggedNumber tag value = encodeTagged tag ⟨encodeDecimal value, encodeDecimal_free value⟩ := by
    simp [encodeTaggedNumber, encodeTagged, encodeTerminated]
  unfold decodeTaggedNumber
  rw [as_tagged, decodeTagged_encodeTagged, some_bind]
  simp only [decodeDecimal_encodeDecimal]
  rfl

/-! ## The Fix frame: BeginString, BodyLength written from the body, the body, CheckSum written from all before it -/

/-- The byte sum the CheckSum field states: every byte ahead of it, modulo 256 -/
def fixChecksum (bytes : List UInt8) : Nat := (bytes.map UInt8.toNat).sum % 256

def fixBodyLengthTag : List UInt8 := [57, 61]
def fixCheckSumTag : List UInt8 := [49, 48, 61]

/-- What the CheckSum is summed over: BeginString (its tag, value and separator, as the venue fixes it),
    the BodyLength the body is counted by, and the body -/
def fixHead (begin : List UInt8) (body : List UInt8) : List UInt8 :=
  begin ++ (encodeTaggedNumber fixBodyLengthTag body.length ++ body)

def encodeFix (begin : List UInt8) (encodeBody : α → List UInt8) (message : α) : List UInt8 :=
  fixHead begin (encodeBody message) ++ (fixCheckSumTag ++ (encodeDigits 3 (fixChecksum (fixHead begin (encodeBody message))) ++ [1]))

/-- A frame read: BeginString as fixed, the length, that many bytes of body, and a CheckSum that sums
    what came before it; the body read whole -/
def decodeFix (begin : List UInt8) (decodeBody : List UInt8 → Option α) (bytes : List UInt8) : Option (α × List UInt8) := do
  let afterBegin ← stripPrefix begin bytes
  let (length, afterLength) ← decodeTaggedNumber fixBodyLengthTag afterBegin
  let (body, afterBody) ← take? length afterLength
  let afterTag ← stripPrefix fixCheckSumTag afterBody
  let (sum, afterSum) ← decodeDigits 3 afterTag
  let rest ← stripPrefix [1] afterSum
  if sum = fixChecksum (fixHead begin body) then
    let message ← decodeBody body
    pure (message, rest)
  else none

theorem decodeFix_encodeFix (begin : List UInt8) (encodeBody : α → List UInt8) (decodeBody : List UInt8 → Option α)
    (roundtrip : ∀ message, decodeBody (encodeBody message) = some message) (message : α) (rest : List UInt8) :
    decodeFix begin decodeBody (encodeFix begin encodeBody message ++ rest) = some (message, rest) := by
  have small : fixChecksum (fixHead begin (encodeBody message)) < 10 ^ 3 := by
    unfold fixChecksum; have := Nat.mod_lt ((List.map UInt8.toNat (fixHead begin (encodeBody message))).sum) (show 256 > 0 by decide); omega
  unfold decodeFix encodeFix fixHead
  simp only [List.append_assoc]
  rw [stripPrefix_append, some_bind]; try dsimp only
  rw [decodeTaggedNumber_encode, some_bind]; try dsimp only
  rw [take?_append rfl, some_bind]; try dsimp only
  rw [stripPrefix_append, some_bind]; try dsimp only
  unfold fixHead at small
  rw [decodeDigits_encodeDigits 3 _ (by simpa [List.append_assoc] using small), some_bind]; try dsimp only
  rw [stripPrefix_append, some_bind]
  simp only [ite_true, roundtrip]
  rfl

/-! ## Fix fields in any order

A Fix message's fields may come in any order between MsgType and CheckSum: the standard fixes only
BeginString, BodyLength and MsgType at its start, CheckSum at its end, and the order inside a repeating
group's entry. So a body is read as the tokens it is, `tag=value` each, and a record takes from them the
tokens of its own tags wherever they stand. Its encoder writes them in the order the specification lists
them, which is one of the orders a decoder accepts. -/

/-- A Fix field as the wire carries it: the digits of its tag, and its value up to the separator -/
structure Token where
  tag : List UInt8
  value : Terminated 1

def Token.encode (token : Token) : List UInt8 :=
  token.tag ++ (61 :: (token.value.val ++ [1]))

/-- A token: its tag up to the equals sign, then its value up to the separator -/
def decodeToken (bytes : List UInt8) : Option (Token × List UInt8) := do
  let (tag, afterTag) ← decodeTerminated 61 bytes
  let (value, rest) ← decodeTerminated 1 afterTag
  pure (⟨tag.val, value⟩, rest)

theorem decodeToken_encode (token : Token) (clean : (61 : UInt8) ∉ token.tag) (rest : List UInt8) :
    decodeToken (token.encode ++ rest) = some (token, rest) := by
  have tag := decodeTerminated_encodeTerminated 61 ⟨token.tag, clean⟩ (token.value.val ++ [1] ++ rest)
  have value := decodeTerminated_encodeTerminated 1 token.value rest
  simp only [encodeTerminated, List.append_assoc, List.singleton_append] at tag value
  simp only [decodeToken, Token.encode, List.append_assoc, List.cons_append, List.nil_append]
  rw [tag, some_bind]
  dsimp only
  rw [value, some_bind]
  rfl

/-- Every token of a body, read until no byte is left; at most one token per byte -/
def decodeTokens : Nat → List UInt8 → Option (List Token)
  | 0, bytes => if bytes.isEmpty then some [] else none
  | fuel + 1, bytes =>
    if bytes.isEmpty then some [] else do
      let (token, rest) ← decodeToken bytes
      let more ← decodeTokens fuel rest
      pure (token :: more)

def encodeTokens (tokens : List Token) : List UInt8 :=
  tokens.flatMap Token.encode

theorem decodeTokens_encodeTokens (tokens : List Token) (clean : ∀ token ∈ tokens, (61 : UInt8) ∉ token.tag)
    (fuel : Nat) (enough : tokens.length ≤ fuel) :
    decodeTokens fuel (encodeTokens tokens) = some tokens := by
  induction tokens generalizing fuel with
  | nil => cases fuel <;> simp [decodeTokens, encodeTokens]
  | cons token others ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have filled : (encodeTokens (token :: others)).isEmpty = false := by
        simp [encodeTokens, Token.encode]
      have first := decodeToken_encode token (clean token (by simp)) (encodeTokens others)
      have more := ih (fun item inside => clean item (by simp [inside])) fuel (by simp at enough; omega)
      simp only [decodeTokens, filled, Bool.false_eq_true, ite_false]
      rw [show encodeTokens (token :: others) = token.encode ++ encodeTokens others by simp [encodeTokens], first,
        some_bind]
      dsimp only
      rw [more, some_bind]
      rfl

/-- The tokens whose tags are among some, in the order they came -/
def select (tags : List (List UInt8)) (tokens : List Token) : List Token :=
  tokens.filter fun token => decide (token.tag ∈ tags)

theorem select_append (tags : List (List UInt8)) (front back : List Token) :
    select tags (front ++ back) = select tags front ++ select tags back := by
  simp [select, List.filter_append]

/-- Part of a record: the tags it may write, and the tokens it wrote, which carry only those tags -/
structure Part where
  tags : List (List UInt8)
  tokens : List Token
  within : ∀ token ∈ tokens, token.tag ∈ tags

/-- The tokens of a record's parts, in the order the specification lists them -/
def encodeParts (parts : List Part) : List Token :=
  parts.flatMap Part.tokens

theorem encodeParts_within (parts : List Part) :
    ∀ token ∈ encodeParts parts, token.tag ∈ (parts.map Part.tags).flatten := by
  intro token inside
  simp only [encodeParts, List.mem_flatMap] at inside
  rcases inside with ⟨part, member, holds⟩
  simp only [List.mem_flatten, List.mem_map]
  exact ⟨part.tags, ⟨part, member, rfl⟩, part.within token holds⟩

/-- Tags no part writes select nothing of the parts' tokens -/
theorem select_apart (tags : List (List UInt8)) (parts : List Part)
    (apart : ∀ tag ∈ tags, tag ∉ (parts.map Part.tags).flatten) :
    select tags (encodeParts parts) = [] := by
  simp only [select, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro token inside mem
  exact apart token.tag mem (encodeParts_within parts token inside)

/-- Selecting one part's tags from the tokens of parts whose tags are all distinct gives that part's tokens -/
theorem select_part (parts : List Part) (tagged : List (List (List UInt8))) (shape : parts.map Part.tags = tagged)
    (distinct : tagged.flatten.Nodup) (k : Nat) (bound : k < tagged.length) :
    select tagged[k] (encodeParts parts) = (parts[k]'(by rw [← shape] at bound; simpa using bound)).tokens := by
  subst shape
  induction parts generalizing k with
  | nil => simp at bound
  | cons part others ih =>
    simp only [List.map_cons, List.flatten_cons, List.nodup_append] at distinct
    rcases distinct with ⟨own, rest, disjoint⟩
    simp only [encodeParts, List.flatMap_cons] at *
    rw [select_append]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.map_cons]
      have whole : select part.tags part.tokens = part.tokens := by
        simp only [select, List.filter_eq_self, decide_eq_true_eq]
        exact part.within
      have none : select part.tags (others.flatMap Part.tokens) = [] := by
        have := select_apart part.tags others (fun tag mem later => disjoint tag mem tag later rfl)
        simpa [encodeParts] using this
      rw [whole, none, List.append_nil]
    | succ k =>
      have inner : k < (others.map Part.tags).length := by simp at bound ⊢; omega
      simp only [List.getElem_cons_succ, List.map_cons]
      have none : select ((others.map Part.tags)[k]'inner) part.tokens = [] := by
        simp only [select, List.filter_eq_nil_iff, decide_eq_true_eq]
        intro token inside mem
        have later : token.tag ∈ (others.map Part.tags).flatten :=
          List.mem_flatten.mpr ⟨_, List.getElem_mem _, mem⟩
        exact disjoint token.tag (part.within token inside) token.tag later rfl
      rw [none, List.nil_append]
      exact ih k rest inner

/-- A field the venue requires: one token of its tag -/
def Part.required (tag : List UInt8) (value : Terminated 1) : Part :=
  ⟨[tag], [⟨tag, value⟩], by simp⟩

/-- A field the venue does not require: one token of its tag, or none -/
def Part.optional (tag : List UInt8) (value : Option (Terminated 1)) : Part :=
  ⟨[tag], (value.map fun item => (⟨tag, item⟩ : Token)).toList, by cases value <;> simp⟩

/-- A required field read: exactly one token of its tag -/
def readRequired (tag : List UInt8) (tokens : List Token) : Option (Terminated 1) :=
  match select [tag] tokens with
  | [token] => some token.value
  | _ => none

/-- An optional field read: no token of its tag, or exactly one -/
def readOptional (tag : List UInt8) (tokens : List Token) : Option (Option (Terminated 1)) :=
  match select [tag] tokens with
  | [] => some none
  | [token] => some (some token.value)
  | _ => none

theorem readRequired_part (tag : List UInt8) (value : Terminated 1) (tokens : List Token)
    (agrees : select [tag] tokens = (Part.required tag value).tokens) : readRequired tag tokens = some value := by
  simp [readRequired, agrees, Part.required]

theorem readOptional_part (tag : List UInt8) (value : Option (Terminated 1)) (tokens : List Token)
    (agrees : select [tag] tokens = (Part.optional tag value).tokens) : readOptional tag tokens = some value := by
  cases value <;> simp [readOptional, agrees, Part.optional]

/-! ## Repeating groups in any order: the count, then entries each led by the delimiter -/

/-- The tokens up to the next that carries the delimiter's tag, and the rest from it -/
def splitBefore (delimiter : List UInt8) : List Token → List Token × List Token
  | [] => ([], [])
  | token :: rest =>
    if token.tag = delimiter then ([], token :: rest)
    else ((token :: (splitBefore delimiter rest).1), (splitBefore delimiter rest).2)

/-- Entries cut where each delimiter stands: every entry leads with it, and holds what follows up to the next -/
def chunks (delimiter : List UInt8) : Nat → List Token → Option (List (List Token))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, token :: rest =>
    if token.tag = delimiter then
      (chunks delimiter fuel (splitBefore delimiter rest).2).map ((token :: (splitBefore delimiter rest).1) :: ·)
    else none

theorem splitBefore_apart (delimiter : List UInt8) (body more : List Token)
    (apart : ∀ token ∈ body, token.tag ≠ delimiter) (next : ∀ token, more.head? = some token → token.tag = delimiter) :
    splitBefore delimiter (body ++ more) = (body, more) := by
  induction body with
  | nil =>
    cases more with
    | nil => rfl
    | cons token rest =>
      have := next token rfl
      simp [splitBefore, this]
  | cons token others ih =>
    have own := apart token (by simp)
    have tail := ih (fun item inside => apart item (by simp [inside]))
    simp [splitBefore, own, tail]

/-- An entry as written: its delimiter, then tokens none of which carries the delimiter's tag -/
def Lead (delimiter : List UInt8) (tokens : List Token) : Prop :=
  ∃ value others, tokens = ⟨delimiter, value⟩ :: others ∧ ∀ token ∈ others, token.tag ≠ delimiter

theorem chunks_entries (delimiter : List UInt8) (entries : List (List Token))
    (led : ∀ entry ∈ entries, Lead delimiter entry) (fuel : Nat) (enough : entries.length ≤ fuel) :
    chunks delimiter fuel entries.flatten = some entries := by
  induction entries generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons entry others ih =>
    rcases led entry (by simp) with ⟨value, body, shaped, apart⟩
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have next : ∀ token, others.flatten.head? = some token → token.tag = delimiter := by
        intro token first
        cases others with
        | nil => simp at first
        | cons entry' more =>
          rcases led entry' (by simp) with ⟨value', body', shaped', _⟩
          subst shaped'
          simp at first
          rw [← first]
      have tail := ih (fun item inside => led item (by simp [inside])) fuel (by simp at enough; omega)
      subst shaped
      have split := splitBefore_apart delimiter body others.flatten apart next
      simp [chunks, split, tail]

/-- A group: its count token, then its entries, or nothing at all where it has none -/
def Part.group (count : List UInt8) (members : List (List UInt8))
    (encode : α → List Token) (within : ∀ item, ∀ token ∈ encode item, token.tag ∈ members) (items : List α) : Part :=
  ⟨count :: members,
   (if items.isEmpty then [] else ⟨count, ⟨encodeDecimal items.length, encodeDecimal_free items.length⟩⟩ :: items.flatMap encode),
   by
     intro token inside
     split at inside
     · simp at inside
     · simp only [List.mem_cons, List.mem_flatMap] at inside
       rcases inside with first | ⟨item, _, holds⟩
       · subst first; simp
       · exact List.mem_cons_of_mem _ (within item token holds)⟩

/-- A group read from its own tokens: none, or the count and exactly that many entries -/
def decodeGroup (count : List UInt8) (delimiter : List UInt8) (decode : List Token → Option α) :
    List Token → Option (List α)
  | [] => some []
  | token :: rest =>
    if token.tag = count then do
      let number ← decodeDecimal token.value.val
      let entries ← chunks delimiter rest.length rest
      if entries.length = number then entries.mapM decode else none
    else none

def readGroup (count : List UInt8) (delimiter : List UInt8) (members : List (List UInt8))
    (decode : List Token → Option α) (tokens : List Token) : Option (List α) :=
  decodeGroup count delimiter decode (select (count :: members) tokens)

theorem mapM_map (encode : α → List Token) (decode : List Token → Option α)
    (roundtrip : ∀ item, decode (encode item) = some item) (items : List α) :
    (items.map encode).mapM decode = some items := by
  induction items with
  | nil => rfl
  | cons item others ih => simp [List.mapM_cons, roundtrip, ih]

theorem flatMap_length_ge (encode : α → List Token) (nonempty : ∀ item, encode item ≠ []) (items : List α) :
    items.length ≤ (items.flatMap encode).length := by
  induction items with
  | nil => simp
  | cons item others ih =>
    have := List.length_pos_iff.mpr (nonempty item)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem readGroup_part (count delimiter : List UInt8) (members : List (List UInt8))
    (encode : α → List Token) (within : ∀ item, ∀ token ∈ encode item, token.tag ∈ members)
    (decode : List Token → Option α) (roundtrip : ∀ item, decode (encode item) = some item)
    (led : ∀ item, Lead delimiter (encode item))
    (items : List α) (tokens : List Token)
    (agrees : select (count :: members) tokens = (Part.group count members encode within items).tokens) :
    readGroup count delimiter members decode tokens = some items := by
  unfold readGroup
  rw [agrees]
  simp only [Part.group]
  cases items with
  | nil => rfl
  | cons item others =>
    have nonempty : ∀ item, encode item ≠ [] := by
      intro item; rcases led item with ⟨_, _, shaped, _⟩; rw [shaped]; simp
    have cut := chunks_entries delimiter ((item :: others).map encode)
      (by intro entry inside; simp only [List.mem_map] at inside; rcases inside with ⟨it, _, rfl⟩; exact led it)
      ((item :: others).flatMap encode).length
      (by rw [List.length_map]; exact flatMap_length_ge encode nonempty _)
    rw [← List.flatMap_def] at cut
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, decodeGroup, ite_true, decodeDecimal_encodeDecimal,
      some_bind, cut, List.length_map, mapM_map encode decode roundtrip]

/-- An entry's tokens lead with its delimiter, where its first part is the delimiter and no later part writes that tag -/
theorem lead_parts (delimiter : List UInt8) (value : Terminated 1) (others : List Part) (tagged : List (List (List UInt8)))
    (shape : others.map Part.tags = tagged) (apart : delimiter ∉ tagged.flatten) :
    Lead delimiter (encodeParts (Part.required delimiter value :: others)) := by
  refine ⟨value, encodeParts others, rfl, ?_⟩
  intro token inside same
  have := encodeParts_within others token inside
  rw [shape, same] at this
  exact apart this

/-! ## A message: MsgType, then the header's parts and the body's, read by tag wherever they stand -/

/-- Is every token one of the record's tags? A message carrying a field its model does not list is not read -/
def known (tagged : List (List (List UInt8))) (tokens : List Token) : Bool :=
  tokens.all fun token => decide (token.tag ∈ tagged.flatten)

theorem known_parts (parts : List Part) (tagged : List (List (List UInt8))) (shape : parts.map Part.tags = tagged) :
    known tagged (encodeParts parts) = true := by
  simp only [known, List.all_eq_true, decide_eq_true_eq]
  intro token inside
  have := encodeParts_within parts token inside
  rwa [shape] at this

/-- The header reads the same from a message's tokens as from its own, where the body writes none of its tags -/
theorem agrees_left (front back : List Part) (frontTags backTags : List (List (List UInt8)))
    (backShape : back.map Part.tags = backTags)
    (apart : ∀ tags ∈ frontTags, ∀ tag ∈ tags, tag ∉ backTags.flatten) :
    ∀ tags ∈ frontTags, select tags (encodeParts (front ++ back)) = select tags (encodeParts front) := by
  intro tags member
  have none := select_apart tags back (by rw [backShape]; exact apart tags member)
  simp only [encodeParts, List.flatMap_append, select_append] at none ⊢
  rw [none, List.append_nil]

/-- The body reads the same from a message's tokens as from its own, where the header writes none of its tags -/
theorem agrees_right (front back : List Part) (frontTags backTags : List (List (List UInt8)))
    (frontShape : front.map Part.tags = frontTags)
    (apart : ∀ tags ∈ backTags, ∀ tag ∈ tags, tag ∉ frontTags.flatten) :
    ∀ tags ∈ backTags, select tags (encodeParts (front ++ back)) = select tags (encodeParts back) := by
  intro tags member
  have none := select_apart tags front (by rw [frontShape]; exact apart tags member)
  simp only [encodeParts, List.flatMap_append, select_append] at none ⊢
  rw [none, List.nil_append]

theorem Token.encode_length (token : Token) : 2 ≤ token.encode.length := by
  simp [Token.encode]; omega

theorem encodeTokens_length_ge (tokens : List Token) : tokens.length ≤ (encodeTokens tokens).length := by
  induction tokens with
  | nil => simp [encodeTokens]
  | cons token others ih =>
    have := Token.encode_length token
    simp only [encodeTokens, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-- A message's bytes: its tokens, each written tag=value and closed by the separator -/
theorem decodeTokens_message (lead : Token) (parts : List Part) (tagged : List (List (List UInt8)))
    (shape : parts.map Part.tags = tagged) (cleanLead : (61 : UInt8) ∉ lead.tag)
    (clean : ∀ tag ∈ tagged.flatten, (61 : UInt8) ∉ tag) :
    decodeTokens (encodeTokens (lead :: encodeParts parts)).length (encodeTokens (lead :: encodeParts parts))
      = some (lead :: encodeParts parts) := by
  apply decodeTokens_encodeTokens _ _ _ (encodeTokens_length_ge _)
  intro token inside
  simp only [List.mem_cons] at inside
  rcases inside with first | later
  · subst first; exact cleanLead
  · have := encodeParts_within parts token later
    rw [shape] at this
    exact clean _ this

/-- A component reads the same from a message's tokens as from its own, where nothing around it writes its tags -/
theorem agrees_slice (front middle back : List Part) (frontTags middleTags backTags : List (List (List UInt8)))
    (frontShape : front.map Part.tags = frontTags) (backShape : back.map Part.tags = backTags)
    (apart : ∀ tags ∈ middleTags, ∀ tag ∈ tags, tag ∉ frontTags.flatten ∧ tag ∉ backTags.flatten) :
    ∀ tags ∈ middleTags, select tags (encodeParts (front ++ middle ++ back)) = select tags (encodeParts middle) := by
  intro tags member
  have before := select_apart tags front (by rw [frontShape]; exact fun tag mem => (apart tags member tag mem).1)
  have after := select_apart tags back (by rw [backShape]; exact fun tag mem => (apart tags member tag mem).2)
  simp only [encodeParts, List.flatMap_append, select_append] at before after ⊢
  rw [before, after, List.nil_append, List.append_nil]

/-! ## Session ends -/

/-- Does an item that ends the session stand only last? Nothing in a packet follows the item that
    ends its session: MoldUdp's zero length message must be the last block of its packet -/
def endsLast (ends : α → Bool) : List α → Bool
  | item :: next :: rest => !ends item && endsLast ends (next :: rest)
  | _ => true

end Omi