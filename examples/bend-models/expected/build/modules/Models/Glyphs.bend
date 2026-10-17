import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanRuntime.bend as R

type Glyph is Data:
  Glyph.g0{}
  Glyph.g1{}
  Glyph.g2{}
  Glyph.g3{}
  Glyph.g4{}
  Glyph.g5{}
  Glyph.g6{}
  Glyph.g7{}
  Glyph.g8{}
  Glyph.g9{}

def encode(+glyph: Glyph) -> List<&2, L.Lean.Int>:
  match glyph:
    case Glyph.g0{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Nil{}}}}}}}}
    case Glyph.g1{}:
      Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}
    case Glyph.g2{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g3{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g4{}:
      Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g5{}:
      Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g6{}:
      Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g7{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}
    case Glyph.g8{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}
    case Glyph.g9{}:
      Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}

def digitOf(+glyph: Glyph) -> Nat:
  match glyph:
    case Glyph.g0{}:
      0n
    case Glyph.g1{}:
      1n
    case Glyph.g2{}:
      2n
    case Glyph.g3{}:
      3n
    case Glyph.g4{}:
      4n
    case Glyph.g5{}:
      5n
    case Glyph.g6{}:
      6n
    case Glyph.g7{}:
      7n
    case Glyph.g8{}:
      8n
    case Glyph.g9{}:
      9n

def segmentCount(+glyph: Glyph) -> Nat:
  match glyph:
    case Glyph.g0{}:
      6n
    case Glyph.g1{}:
      2n
    case Glyph.g2{}:
      5n
    case Glyph.g3{}:
      5n
    case Glyph.g4{}:
      4n
    case Glyph.g5{}:
      5n
    case Glyph.g6{}:
      6n
    case Glyph.g7{}:
      3n
    case Glyph.g8{}:
      7n
    case Glyph.g9{}:
      6n

def isEight(+glyph: Glyph) -> Bool:
  match glyph:
    case Glyph.g0{}:
      False{}
    case Glyph.g1{}:
      False{}
    case Glyph.g2{}:
      False{}
    case Glyph.g3{}:
      False{}
    case Glyph.g4{}:
      False{}
    case Glyph.g5{}:
      False{}
    case Glyph.g6{}:
      False{}
    case Glyph.g7{}:
      False{}
    case Glyph.g8{}:
      True{}
    case Glyph.g9{}:
      False{}

law encode_width:
  for +glyph: Glyph
  {R.LexLeanRuntime.length.List(L.Lean.Int, encode(glyph)) == 7n : Nat}

def encode_width(glyph):
  match glyph:
    case Glyph.g0{}:
      {==}
    case Glyph.g1{}:
      {==}
    case Glyph.g2{}:
      {==}
    case Glyph.g3{}:
      {==}
    case Glyph.g4{}:
      {==}
    case Glyph.g5{}:
      {==}
    case Glyph.g6{}:
      {==}
    case Glyph.g7{}:
      {==}
    case Glyph.g8{}:
      {==}
    case Glyph.g9{}:
      {==}
