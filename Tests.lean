import NestCore
import NestUnit
import Klg.Fixed32
import Klg.Fixed64

open Pod
open Nest.Core
open Nest.Unit
open Klg

variable {α : Type} {n : Nat}
  [ToString α] [Inhabited α] [BEq α] [OfNat α n] [OfScientific α]
  [Add α] [Sub α] [Mul α] [Div α] [Mod α] [Neg α]
  [DecidableEq α] [le : LE α] [lt : LT α] [DecidableRel le.le] [DecidableRel lt.lt]

def num (f : String → Option α) (s : String) : UnitM α := do
  let x := f s
  assert x.isSome
  pure $ x.getD default

def parseTest (f : String → Option α) (s : String) : UnitM Unit := do
  num f s >>= λ x ↦ assert $ toString x = s

def f32eq (x y e : Float32) : Bool := (x - y).abs < e
def f64eq (x y e : Float) : Bool := (x - y).abs < e

def fpTests (ty : String) [∀{n}, OfNat α n]
  (zero one half epsilon : α)
  (parse : String → Option α)
  (toNat : α → Nat)
  (toInt : α → Int)
  (toFloat : α → Float)
  (toFloat32 : α → Float32)
  (ofNat : Nat → α)
  (ofFloat : Float → α)
  (ofFloat32 : Float32 → α)
  (sgn trunc ceil floor round abs sqrt : α → α)
  (extra : List TestTree)
  : TestTree :=
  let num := num parse
  let parseTest := parseTest parse
  let rbeq (x y : α) : Bool := abs (x - y) < epsilon
  .group ty $ [
    .group "Exact parse & toString" [
      .unitTest "0" (parseTest "0"),
      .unitTest "0.5" (parseTest "0.5"),
      .unitTest "0.7625" (parseTest "0.875"),
      .unitTest "-1" (parseTest "-1"),
      .unitTest "-4.125" (parseTest "-4.125"),
      .unitTest "2" (parseTest "20"),
      .unitTest "10" (parseTest "10"),
      .unitTest "1" (parseTest "1"),
      .unitTest "Leading/trailing zeros" do assert $ (← num "001.5") = (← num "1.500")
    ],
    .group "Constants" [
      .unitTest "zero" (assert $ zero == 0),
      .unitTest "one" (assert $ one == 1),
      .unitTest "half" (assert $ half == 0.5)
    ],
    .group "Conversions" [
      .unitTest "toNat 1.5 = 1" (assert $ toNat 1.5 = 1),
      .unitTest "toNat 156.875 = 156" (assert $ toNat 156.875 = 156),
      .unitTest "toInt -28 = -28" (assert $ toInt (-28) = -28),
      .unitTest "toInt -0.5 = 0" (assert $ toInt (-0.5) = 0),
      .unitTest "toInt 12 = 12" (assert $ toInt 12 = 12),
      .unitTest "toInt 2.7 = 2" (assert $ toInt 2.7 = 2),
      .unitTest "toFloat 7.8 ≈ 7.8" (assert $ f64eq (toFloat 7.8) 7.8 1e-4),
      .unitTest "toFloat -13.6 ≈ -13.6" (assert $ f64eq (toFloat (-13.6)) (-13.6) 1e-4),
      .unitTest "toFloat32 7.8 ≈ 7.8" (assert $ f32eq (toFloat32 7.8) 7.8 1e-4),
      .unitTest "toFloat32 -13.6 ≈ -13.6" (assert $ f32eq (toFloat32 (-13.6)) (-13.6) 1e-4),
      .unitTest "ofNat 45 = 45" do assert $ ofNat 45 = (← num "45"),
      .unitTest "ofFloat -0.01 ≈ -0.01" do assert $ rbeq (ofFloat $ -0.01) (← num "-0.01"),
      .unitTest "ofFloat 99.9 ≈ 99.9" do assert $ rbeq (ofFloat 99.9) (← num "99.9"),
      .unitTest "ofFloat32 0.1 ≈ 0.1" do assert $ rbeq (ofFloat32 0.1) (← num "0.1"),
      .unitTest "ofFloat32 -4.8 ≈ -4.8" do assert $ rbeq (ofFloat32 $ -4.8) (← num "-4.8")
    ],
    .group "Negate" [
      .unitTest "-(1) = -1" do assert $ -1 == (← num "-1"),
      .unitTest "-(-2) = 2" do assert $ -(← num "-2") == 2,
      .unitTest "-(0) = 0" do assert $ -0 == 0,
      .unitTest "-(1.5) = -1.5" do assert $ -1.5 == (← num "-1.5"),
      .unitTest "-(-1.5) = 1.5" do assert $ -(← num "-1.5") == 1.5
    ],
    .group "Sign" [
      .unitTest "sgn -1 = -1" $ assert $ sgn (-1) = -1,
      .unitTest "sgn 0.2 = 1" $ assert $ sgn 0.2 = 1,
      .unitTest "sgn -0.99 = -1" $ assert $ sgn (-0.99) = -1,
      .unitTest "sgn 0 = 1" $ assert $ sgn 0 = 1
    ],
    .group "Trunc" [
      .unitTest "trunc 0 = 0" $ assert $ trunc 0 = 0,
      .unitTest "trunc 1 = 1" $ assert $ trunc 1 = 1,
      .unitTest "trunc -1 = -1" $ assert $ trunc (-1) = -1,
      .unitTest "trunc 1.5 = 1" $ assert $ trunc 1.5 = 1,
      .unitTest "trunc -1.5 = -1" $ assert $ trunc (-1.5) = -1
    ],
    .group "Ceil" [
      .unitTest "ceil 0 = 0" $ assert $ ceil 0 = 0,
      .unitTest "ceil 1 = 1" $ assert $ ceil 1 = 1,
      .unitTest "ceil -1 = -1" $ assert $ ceil (-1) = -1,
      .unitTest "ceil 1.5 = 2" $ assert $ ceil 1.5 = 2,
      .unitTest "ceil -1.5 = -1" $ assert $ ceil (-1.5) = -1
    ],
    .group "Floor" [
      .unitTest "floor 0 = 0" $ assert $ floor 0 = 0,
      .unitTest "floor 1 = 1" $ assert $ floor 1 = 1,
      .unitTest "floor -1 = -1" $ assert $ floor (-1) = -1,
      .unitTest "floor 1.5 = 1" $ assert $ floor 1.5 = 1,
      .unitTest "floor -1.5 = -2" $ assert $ floor (-1.5) = -2
    ],
    .group "Round" [
      .unitTest "round 0 = 0" $ assert $ round 0 = 0,
      .unitTest "round 1 = 1" $ assert $ round 1 = 1,
      .unitTest "round -1 = -1" $ assert $ round (-1) = -1,
      .unitTest "round 1.5 = 2" $ assert $ round 1.5 = 2,
      .unitTest "round -1.5 = -2" $ assert $ round (-1.5) = -2
    ],
    .group "Absolute" [
      .unitTest "abs 0 = 0" $ assert $ abs 0 = 0,
      .unitTest "abs 1 = 1" $ assert $ abs 1 = 1,
      .unitTest "abs -2 = 2" $ assert $ abs (-2) = 2,
      .unitTest "abs -1.5 = 1.5" $ assert $ abs (-1.5) = 1.5,
      .unitTest "abs -0.5 = 0.5" $ assert $ abs (-0.5) = 0.5,
      .unitTest "abs 0.25 = 0.25" $ assert $ abs 0.25 = 0.25
    ],
    .group "Square root" [
      .unitTest "sqrt 4 ≈ 2" $ assert $ rbeq (sqrt 4) 2,
      .unitTest "sqrt 1 ≈ 1" $ assert $ rbeq (sqrt 1) 1,
      .unitTest "sqrt 0.25 ≈ 0.5" $ assert $ rbeq (sqrt 0.25) 0.5,
      .unitTest "sqrt -1 = 0" $ assert $ sqrt (-1) = 0,
      .unitTest "sqrt 0.5 = 0" $ assert $ sqrt (-0.5) = 0
    ],
    .group "Add" [
      .unitTest "0 + 0 = 0" $ assert $ (0 : α) + 0 = 0,
      .unitTest "0 + 0 = 0" $ assert $ (0 : α) + 1 = 1,
      .unitTest "0 + 0 = 0" $ assert $ (1 : α) + 1 = 2,
      .unitTest "0 + 0 = 0" $ assert $ (0.5 : α) + 1.5 = 2,
      .unitTest "0 + 0 = 0" $ assert $ (0.5 : α) + -1.5 = -1
    ],
    .group "Subtract" [
      .unitTest "0 - 0 = 0" $ assert $ (0 : α) - 0 = 0,
      .unitTest "0 - 1 = -1" $ assert $ (0 : α) - 1 = -1,
      .unitTest "1 - 1 = 0" $ assert $ (1 : α) - 1 = 0,
      .unitTest "1.5 - -0.5 = 2" $ assert $ (1.5 : α) - -0.5 = 2,
      .unitTest "0.5 - 2 = -1.5" $ assert $ (0.5 : α) - 2 = -1.5
    ],
    .group "Multiply" [
      .unitTest "0 * 0 = 0" $ assert $ (0 : α) * 0 = 0,
      .unitTest "0 * 1.5 = 0" $ assert $ (0 : α) * 1.5 = 0,
      .unitTest "-1.5 * 1 = -1.5" $ assert $ (-1.5 : α) * 1 = -1.5,
      .unitTest "0.5 * -2 = -1" $ assert $ (0.5 : α) * -2 = -1,
      .unitTest "-1 * -2 = 2" $ assert $ (-1 : α) * -2 = 2
    ],
    .group "Divide" [
      .unitTest "-1 / 2 = -0.5" $ assert $ (-1 : α) / 2 = -0.5,
      .unitTest "1 / 0.5 = 2" $ assert $ (1 : α) / 0.5 = 2,
      .unitTest "-1 / -2 = 0.5" $ assert $ (-1 : α) / -2 = 0.5,
      .unitTest "0.5 / 2 = 0.25" $ assert $ (0.5 : α) / 2 = 0.25,
      .unitTest "-0.5 / 0.25 = -2" $ assert $ (-0.5 : α) / 0.25 = -2
    ],
    .group "Less" [
      .unitTest "0.5 < 1" $ assert $ (0.5 : α) < 1,
      .unitTest "0 < 0.25" $ assert $ (0 : α) < 0.25,
      .unitTest "-2 < 0.5" $ assert $ (-2 : α) < 0.5,
      .unitTest "-0.5 < 0.25" $ assert $ (-0.5 : α) < 0.25
    ],
    .group "Less or equal" [
      .unitTest "0 ≤ 0" $ assert $ (0 : α) ≤ 0,
      .unitTest "1 ≤ 2" $ assert $ (1 : α) ≤ 2,
      .unitTest "-2 ≤ 0.25" $ assert $ (-2 : α) ≤ 0.25
    ]
  ] ++ extra

def main : IO UInt32 := do
  Nest.Core.defaultMain $ .group "Tests" [
    fpTests "Fixed32"
      Fixed32.zero Fixed32.one Fixed32.half (.ofFloat 1e-4) Fixed32.parse
      Fixed32.toNat Fixed32.toInt Fixed32.toFloat
      Fixed32.toFloat32 Fixed32.ofNat Fixed32.ofFloat Fixed32.ofFloat32
      Fixed32.sgn Fixed32.trunc Fixed32.ceil Fixed32.floor Fixed32.round Fixed32.abs Fixed32.sqrt
      [
        .group "toInt32" [
          .unitTest "toInt32 -13 = -13" do assert (Fixed32.toInt32 (-13) = -13),
          .unitTest "toInt32 0.9 = 0" do assert (Fixed32.toInt32 0.9 = 0),
          .unitTest "toInt32 10.9 = 10" do assert (Fixed32.toInt32 10.9 = 10)
        ]
      ],
    fpTests "Fixed64"
      Fixed64.zero Fixed64.one Fixed64.half (.ofFloat 1e-4) Fixed64.parse
      Fixed64.toNat Fixed64.toInt Fixed64.toFloat
      Fixed64.toFloat32 Fixed64.ofNat Fixed64.ofFloat Fixed64.ofFloat32
      Fixed64.sgn Fixed64.trunc Fixed64.ceil Fixed64.floor Fixed64.round Fixed64.abs Fixed64.sqrt
      [
        .group "toInt64" [
          .unitTest "toInt64 -13 = -13" do assert (Fixed64.toInt64 (-13) = -13),
          .unitTest "toInt64 0.9 = 0" do assert (Fixed64.toInt64 0.9 = 0),
          .unitTest "toInt64 10.9 = 10" do assert (Fixed64.toInt64 10.9 = 10)
        ]
      ]
  ]
