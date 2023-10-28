import Pod.Int
import Pod.Float

open Pod (Int32 Int64 Float32)

namespace Klg

/-- Fixed point number with a sign, 15 integer bits and 16 fractional bits. -/
structure Fixed32 where
  val : UInt32
deriving Inhabited, Repr

namespace Fixed32

def fractionalBitsSize : Nat := 16
def fractionalBitsSize' : UInt32 := fractionalBitsSize.toUInt32
def integralBitsSize : Nat := 16
def integralBitsSize' : UInt32 := integralBitsSize.toUInt32
def fractionalBitsMask : UInt32 := (1 <<< fractionalBitsSize') - 1
def integralBitsMask : UInt32 := ~~~fractionalBitsMask
def zero : Fixed32 := .mk 0
def one : Fixed32 := .mk $ 1 <<< fractionalBitsSize'
def half : Fixed32 := .mk $ 1 <<< (fractionalBitsSize' - 1)

def ofUInt16 (x : UInt16) : Fixed32 :=
  .mk $ x.toUInt32 <<< fractionalBitsSize'

def ofNat (n : Nat) : Fixed32 :=
  .ofUInt16 n.toUInt16

def toUInt16 (x : Fixed32) : UInt16 :=
  (x.val >>> fractionalBitsSize').toUInt16

def toInt32 (x : Fixed32) : Int32 :=
  (Int32.mk x.val).sar (Int32.mk fractionalBitsSize')

def toNat (x : Fixed32) : Nat :=
  x.toUInt16.toNat

def sign (x : Fixed32) : Bool :=
  (x.val &&& ((1 : UInt32) <<< 31)) > 0

/-- Returns `-1` for negative inputs and `1` for non-negative. -/
def sgn (x : Fixed32) : Fixed32 :=
  Fixed32.mk $ Int32.val $ Neg.neg $ Int32.mk $
    ((x.val &&& ((1 : UInt32) <<< 31)) >>> (integralBitsSize' - 2)) - (1 <<< fractionalBitsSize')

def toInt (x : Fixed32) : Int :=
  if x.sign
    then Int.negOfNat (Fixed32.mk (x.val - 1).complement).toUInt16.toNat
    else Int.ofNat x.toNat

def toFloat (x : Fixed32) : Float :=
  (Int32.mk x.val).toFloat / ((1 : UInt64) <<< fractionalBitsSize.toUInt64).toFloat

def ofFloat (x : Float) : Fixed32 :=
  .mk $ Int32.val $ Int32.ofFloat $ x * (1 <<< fractionalBitsSize.toUInt64).toFloat

def toFloat32 (x : Fixed32) : Float32 :=
  (Int32.mk x.val).toFloat32 / ((1 : UInt64) <<< fractionalBitsSize.toUInt64).toFloat32

def ofFloat32 (x : Float32) : Fixed32 :=
  .mk $ Int32.val $ Float32.toInt32 $ x * (1 <<< fractionalBitsSize.toUInt64).toFloat32

/-- Round towards zero. -/
def trunc (x : Fixed32) : Fixed32 :=
  let negative := x.val >>> 31
  let fracNz := UInt32.ofBool $ x.val &&& fractionalBitsMask > 0
  .mk $
    (x.val &&& integralBitsMask) + ((negative &&& fracNz) <<< fractionalBitsSize')

/-- Round towards positive infinity. -/
def ceil (x : Fixed32) : Fixed32 :=
  let fracNz := UInt32.ofBool $ x.val &&& fractionalBitsMask > 0
  .mk $
    (x.val &&& integralBitsMask) + (fracNz <<< fractionalBitsSize')

/-- Round towards negative infinity. -/
def floor (x : Fixed32) : Fixed32 :=
  .mk $ x.val &&& integralBitsMask

def abs (x : Fixed32) : Fixed32 :=
  let sign := x.val >>> 31
  mk $ (x.val - sign) ^^^ (0 - sign)

/-- Round (x+0.5) towards infinity. -/
def round (x : Fixed32) : Fixed32 :=
  let sign := x.val >>> 31
  -- trunc $ mk $ x.val + ((half.val - sign) ^^^ (0 - sign))
  .mk $ (((x.abs.val + half.val) &&& integralBitsMask) - sign) ^^^ (0 - sign)

def blt (x y : Fixed32) : Bool :=
  (Int32.mk x.val).blt (Int32.mk y.val)

def ble (x y : Fixed32) : Bool :=
  (Int32.mk x.val).ble (Int32.mk y.val)

instance : Add Fixed32 where
  add x y := .mk $ x.val + y.val

instance : Sub Fixed32 where
  sub x y := .mk $ x.val - y.val

instance : Neg Fixed32 where
  neg x := .mk (x.val - 1).complement

instance : Mul Fixed32 where
  mul x y := .mk
    ((Int32.mk x.val).toInt64 * (Int32.mk y.val).toInt64 >>>
      (Int32.mk fractionalBitsSize').toInt64).toInt32.val
    -- let xi := Int32.mk x.val >>> Int32.mk fractionalBitsSize'
    -- let yi := Int32.mk y.val >>> Int32.mk fractionalBitsSize'
    -- let xf := Int32.mk $ x.val &&& fractionalBitsMask
    -- let yf := Int32.mk $ y.val &&& fractionalBitsMask
    -- .mk $ Int32.val $
    --   ((xi * yi) <<< Int32.mk fractionalBitsSize') +
    --   (xi * yf) + (xf * yi) +
    --   (((xf * yf) >>> Int32.mk fractionalBitsSize') &&& Int32.mk fractionalBitsMask)

instance : Div Fixed32 where
  div x y :=
    .mk $ Int32.val $ Int64.toInt32 $
      ((Int32.mk x.val).toInt64 <<< (Int32.mk fractionalBitsSize').toInt64) / (Int32.mk y.val).toInt64

def sqrt (x : Fixed32) (approx : Fixed32 := .ofFloat 1.0) (fuel : Nat := 8) :=
  if x.val >>> 31 > 0
    then zero
    else
      match fuel with
      | 0 => approx
      | fuel+1 =>
        let approx := mk $ Int32.val $ Int32.mk (approx + x / approx).val >>> Int32.mk 1
        sqrt x approx fuel

instance : BEq Fixed32 where
  beq x y := x.val == y.val

instance : LT Fixed32 where
  lt x y := x.blt y

instance : LE Fixed32 where
  le x y := x.ble y

instance : DecidableEq Fixed32 := λ x y ↦
  if h: x.val = y.val
    then by
      apply isTrue
      show ({ val := x.val } : Fixed32) = _
      rw [h]
    else by
      apply isFalse
      intro h'
      rewrite [h'] at h
      contradiction

instance {x y : Fixed32} : Decidable (x < y) :=
  if h: x.blt y
    then isTrue h
    else by
      apply isFalse
      intro
      contradiction

instance {x y : Fixed32} : Decidable (x ≤ y) :=
  if h: x.ble y
    then isTrue h
    else by
      apply isFalse
      intro
      contradiction

private
def binFracToDec (x : UInt64) (i : Nat) (p acc : Nat := 0) : Nat :=
  let acc := (acc * 10) + ite ((x &&& (1 <<< i.toUInt64)) > 0) (5 ^ (p + 1)) 0
  if h: i > 0
    then
      have : i - 1 < i := Nat.sub_lt h (by decide)
      binFracToDec x (i - 1) (p + 1) acc
    else acc
termination_by _ => i

protected
def binFracToDecStr (x : UInt64) (i : Nat) : String :=
  let n := binFracToDec x i
  if n = 0
    then ""
    else
      let s := toString n
      let left := i + 1 - s.length
      (List.replicate left "0").foldl (.++.) "" ++ s.dropRightWhile (· == '0')

instance : ToString Fixed32 where
  toString x :=
    let (s, x) := ite x.sign ("-", -x) ("", x)
    let i := x.val >>> fractionalBitsSize'
    let f := Klg.Fixed32.binFracToDecStr x.val.toUInt64 (fractionalBitsSize - 1)
    let f := ite (f.length == 0) "" ("." ++ f)
    s!"{s}{i}{f}"

def parse (s : String) : Option Fixed32 := do
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
        some $ .mk ((i <<< fractionalBitsSize) + f).toUInt32
      else none
  | _ => none
  pure $ if sign
    then -pos
    else pos

instance {n} : OfNat Fixed32 n := ⟨Fixed32.ofNat n⟩

instance : OfScientific Fixed32 where
  ofScientific m s e := Fixed32.ofFloat $ OfScientific.ofScientific m s e
