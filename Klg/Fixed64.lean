import Klg.Fixed32

open Pod (Int32 Int64 Float32)

namespace Klg

/-- Fixed point number with a sign, 31 integer bits and 32 fractional bits. -/
structure Fixed64 where
  val : UInt64
deriving Inhabited, Repr

namespace Fixed64

def fractionalBitsSize : Nat := 32
def fractionalBitsSize' : UInt64 := fractionalBitsSize.toUInt64
def integralBitsSize : Nat := 32
def integralBitsSize' : UInt64 := integralBitsSize.toUInt64
def fractionalBitsMask : UInt64 := (1 <<< fractionalBitsSize') - 1
def integralBitsMask : UInt64 := ~~~fractionalBitsMask
def zero : Fixed64 := .mk 0
def one : Fixed64 := .mk $ 1 <<< fractionalBitsSize'
def half : Fixed64 := .mk $ 1 <<< (fractionalBitsSize' - 1)

def sign (x : Fixed64) : Bool :=
  (x.val &&& ((1 : UInt64) <<< 63)) > 0

/-- Returns `-1` for negative inputs and `1` for non-negative. -/
def sgn (x : Fixed64) : Fixed64 :=
  Fixed64.mk $ Int64.val $ Neg.neg $ Int64.mk $
    ((x.val &&& ((1 : UInt64) <<< 63)) >>> (integralBitsSize' - 2)) - (1 <<< fractionalBitsSize')

def ofUInt32 (x : UInt32) : Fixed64 :=
  .mk $ x.toUInt64 <<< fractionalBitsSize'

def ofNat (n : Nat) : Fixed64 :=
  .ofUInt32 n.toUInt32

def toUInt32 (x : Fixed64) : UInt32 :=
  (x.val >>> fractionalBitsSize').toUInt32

def toInt64 (x : Fixed64) : Int64 :=
  (Int64.mk x.val).sar (Int64.mk fractionalBitsSize')

def toNat (x : Fixed64) : Nat :=
  x.toUInt32.toNat

def toInt (x : Fixed64) : Int :=
  if x.sign
    then Int.negOfNat (Fixed64.mk (x.val - 1).complement).toUInt32.toNat
    else Int.ofNat x.toNat

def toFloat (x : Fixed64) : Float :=
  (Int64.mk x.val).toFloat / ((1 : UInt64) <<< fractionalBitsSize.toUInt64).toFloat

def ofFloat (x : Float) : Fixed64 :=
  .mk $ Int64.val $ Int64.ofFloat $ x * (1 <<< fractionalBitsSize.toUInt64).toFloat

def toFloat32 (x : Fixed64) : Float32 :=
  (Int64.mk x.val).toFloat32 / ((1 : UInt64) <<< fractionalBitsSize.toUInt64).toFloat32

def ofFloat32 (x : Float32) : Fixed64 :=
  .mk $ Int64.val $ Float32.toInt64 $ x * (1 <<< fractionalBitsSize.toUInt64).toFloat32

/-- Round towards zero. -/
def trunc (x : Fixed64) : Fixed64 :=
  let negative := x.val >>> 63
  let fracNz := UInt64.ofBool $ x.val &&& fractionalBitsMask > 0
  .mk $
    (x.val &&& integralBitsMask) + ((negative &&& fracNz) <<< fractionalBitsSize')

/-- Round towards positive infinity. -/
def ceil (x : Fixed64) : Fixed64 :=
  let fracNz := UInt64.ofBool $ x.val &&& fractionalBitsMask > 0
  .mk $
    (x.val &&& integralBitsMask) + (fracNz <<< fractionalBitsSize')

/-- Round towards negative infinity. -/
def floor (x : Fixed64) : Fixed64 :=
  .mk $ x.val &&& integralBitsMask

def abs (x : Fixed64) : Fixed64 :=
  let sign := x.val >>> 63
  mk $ (x.val - sign) ^^^ (0 - sign)

/-- Round (x+0.5) towards infinity. -/
def round (x : Fixed64) : Fixed64 :=
  let sign := x.val >>> 63
  -- trunc $ .mk $ x.val + ((half.val - sign) ^^^ (0 - sign))
  .mk $ (((x.abs.val + half.val) &&& integralBitsMask) - sign) ^^^ (0 - sign)

def blt (x y : Fixed64) : Bool :=
  (Int64.mk x.val).blt (Int64.mk y.val)

def ble (x y : Fixed64) : Bool :=
  (Int64.mk x.val).ble (Int64.mk y.val)

instance : Add Fixed64 where
  add x y := .mk $ x.val + y.val

instance : Sub Fixed64 where
  sub x y := .mk $ x.val - y.val

instance : Neg Fixed64 where
  neg x := .mk (x.val - 1).complement

instance : Mul Fixed64 where
  mul x y :=
    let xi := Int64.mk x.val >>> Int64.mk fractionalBitsSize'
    let yi := Int64.mk y.val >>> Int64.mk fractionalBitsSize'
    let xf := Int64.mk $ x.val &&& fractionalBitsMask
    let yf := Int64.mk $ y.val &&& fractionalBitsMask
    .mk $ Int64.val $
      ((xi * yi) <<< Int64.mk fractionalBitsSize') +
      (xi * yf) + (xf * yi) +
      (((xf * yf) >>> Int64.mk fractionalBitsSize') &&& Int64.mk fractionalBitsMask)

instance : Div Fixed64 where
  div x y :=
    let ysign := y.val >>> 63
    mk $ (((x * (mk $ ((1 : UInt64) <<< 63) / y.abs.val)).val <<< 1) - ysign) ^^^ (0 - ysign)

def sqrt (x : Fixed64) (approx : Fixed64 := .ofFloat 1.0) (fuel : Nat := 16) :=
  if x.val >>> 63 > 0
    then zero
    else
      match fuel with
      | 0 => approx
      | fuel+1 =>
        let approx := mk $ Int64.val $ Int64.mk (approx + x / approx).val >>> Int64.mk 1
        sqrt x approx fuel

instance : BEq Fixed64 where
  beq x y := x.val == y.val

instance : LT Fixed64 where
  lt x y := x.blt y

instance : LE Fixed64 where
  le x y := x.ble y

instance : DecidableEq Fixed64 := λ x y ↦
  if h: x.val = y.val
    then by
      apply isTrue
      show ({ val := x.val } : Fixed64) = _
      rw [h]
    else by
      apply isFalse
      intro h'
      rewrite [h'] at h
      contradiction

instance {x y : Fixed64} : Decidable (x < y) :=
  if h: x.blt y
    then isTrue h
    else by
      apply isFalse
      intro
      contradiction

instance {x y : Fixed64} : Decidable (x ≤ y) :=
  if h: x.ble y
    then isTrue h
    else by
      apply isFalse
      intro
      contradiction

instance : ToString Fixed64 where
  toString x :=
    let (s, x) := ite x.sign ("-", -x) ("", x)
    let i := x.val >>> fractionalBitsSize'
    let f := Klg.Fixed32.binFracToDecStr x.val (fractionalBitsSize - 1)
    let f := ite (f.length == 0) "" ("." ++ f)
    s!"{s}{i}{f}"

def parse (s : String) : Option Fixed64 := do
  let (s, sign) := if s.front == '-'
    then (s.drop 1, true)
    else (s, false)
  let max := 1 <<< (integralBitsSize - 1)
  let pos ← match s.splitOn "." with
  | i :: [] => do
    let i ← i.toNat?
    if (i < max) || (sign && i == max)
      then some $ ofNat i
      else none
  | i :: f :: [] => do
    let i ← i.toNat?
    let f' ← f.toNat?
    if (i < max) || (sign && i == max)
      then
        let f := f' * (1 <<< fractionalBitsSize) / (Nat.pow 10 f.length)
        some $ .mk ((i <<< fractionalBitsSize) + f).toUInt64
      else none
  | _ => none
  pure $ if sign
    then -pos
    else pos

instance {n} : OfNat Fixed64 n := ⟨Fixed64.ofNat n⟩

instance : OfScientific Fixed64 where
  ofScientific m s e := Fixed64.ofFloat $ OfScientific.ofScientific m s e
