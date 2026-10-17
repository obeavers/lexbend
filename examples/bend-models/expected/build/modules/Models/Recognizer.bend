import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanRuntime.bend as R
import ../LexLeanLinArith.bend as LA
import ./Glyphs.bend as Models_Glyphs

def hiddenWeights.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(4), Con{R.Lean.UInt8.lit(3), Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(253), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(252), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(3), Con{R.Lean.UInt8.lit(0), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def hiddenWeights() -> List<&2, List<&2, L.Lean.Int>>:
  Con{Con{L.ofNat{4n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{4n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{4n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{4n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{4n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{4n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{4n}, Nil{}}}}}}}}, Con{Con{L.ofNat{3n}, Con{L.negSucc{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.negSucc{0n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.negSucc{2n}, Con{L.ofNat{1n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Con{Con{L.negSucc{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.negSucc{1n}, Nil{}}}}}}}}, Con{Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Con{L.ofNat{1n}, Nil{}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.negSucc{3n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{3n}, Con{L.ofNat{0n}, Nil{}}}}}}}}, Nil{}}}}}}}}}}}}}

law hiddenWeights.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(1n, True{}, S.Sem.flatten(L.Lean.Int, hiddenWeights()), hiddenWeights.bytes()), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, hiddenWeights()), 12n), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, hiddenWeights()), 12n), S.Sem.lengthsAre(L.Lean.Int, hiddenWeights(), 7n)))) == True{} : Bool}

def hiddenWeights.decoded():
  {==}

def hiddenBias.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(1), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(3), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(251), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def hiddenBias() -> List<&2, L.Lean.Int>:
  Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{1n}, Con{L.negSucc{1n}, Con{L.ofNat{3n}, Con{L.negSucc{4n}, Con{L.ofNat{2n}, Nil{}}}}}}}}}}}}}

law hiddenBias.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(4n, True{}, hiddenBias(), hiddenBias.bytes()), L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, hiddenBias()), 12n)) == True{} : Bool}

def hiddenBias.decoded():
  {==}

def outputWeights.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(2), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(0), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def outputWeights() -> List<&2, List<&2, L.Lean.Int>>:
  Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Con{Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{2n}, Con{L.ofNat{2n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Con{L.ofNat{0n}, Nil{}}}}}}}}}}}}}, Nil{}}}}}}}}}}}

law outputWeights.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(1n, True{}, S.Sem.flatten(L.Lean.Int, outputWeights()), outputWeights.bytes()), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, outputWeights()), 10n), L.Lean.Bool.and(L.Lean.Nat.beq(L.Lean.List.length(List<&2, L.Lean.Int>, outputWeights()), 10n), S.Sem.lengthsAre(L.Lean.Int, outputWeights(), 12n)))) == True{} : Bool}

def outputWeights.decoded():
  {==}

def outputBias.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(250), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(254), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(251), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(251), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(252), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(251), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(250), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(253), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(249), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(250), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Con{R.Lean.UInt8.lit(255), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def outputBias() -> List<&2, L.Lean.Int>:
  Con{L.negSucc{5n}, Con{L.negSucc{1n}, Con{L.negSucc{4n}, Con{L.negSucc{4n}, Con{L.negSucc{3n}, Con{L.negSucc{4n}, Con{L.negSucc{5n}, Con{L.negSucc{2n}, Con{L.negSucc{6n}, Con{L.negSucc{5n}, Nil{}}}}}}}}}}}

law outputBias.decoded:
  {L.Lean.Bool.and(R.LexLeanModels.tensorMatches(4n, True{}, outputBias(), outputBias.bytes()), L.Lean.Nat.beq(L.Lean.List.length(L.Lean.Int, outputBias()), 10n)) == True{} : Bool}

def outputBias.decoded():
  {==}

def digitNames.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(122), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(114), Con{R.Lean.UInt8.lit(111), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(111), Con{R.Lean.UInt8.lit(110), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(116), Con{R.Lean.UInt8.lit(119), Con{R.Lean.UInt8.lit(111), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(116), Con{R.Lean.UInt8.lit(104), Con{R.Lean.UInt8.lit(114), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(102), Con{R.Lean.UInt8.lit(111), Con{R.Lean.UInt8.lit(117), Con{R.Lean.UInt8.lit(114), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(102), Con{R.Lean.UInt8.lit(105), Con{R.Lean.UInt8.lit(118), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(115), Con{R.Lean.UInt8.lit(105), Con{R.Lean.UInt8.lit(120), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(115), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(118), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(110), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(105), Con{R.Lean.UInt8.lit(103), Con{R.Lean.UInt8.lit(104), Con{R.Lean.UInt8.lit(116), Con{R.Lean.UInt8.lit(10), Con{R.Lean.UInt8.lit(110), Con{R.Lean.UInt8.lit(105), Con{R.Lean.UInt8.lit(110), Con{R.Lean.UInt8.lit(101), Con{R.Lean.UInt8.lit(10), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def digitNames() -> List<&2, String>:
  Con{"zero", Con{"one", Con{"two", Con{"three", Con{"four", Con{"five", Con{"six", Con{"seven", Con{"eight", Con{"nine", Nil{}}}}}}}}}}}

law digitNames.decoded:
  {R.LexLeanModels.linesMatch(digitNames(), digitNames.bytes()) == True{} : Bool}

def digitNames.decoded():
  {==}

def banner.bytes() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(76), Con{R.Lean.UInt8.lit(76), Con{R.Lean.UInt8.lit(77), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(1), Nil{}}}}}}}

def banner() -> R.Lean.ByteArray:
  R.Lean.ByteArray.mk{Con{R.Lean.UInt8.lit(76), Con{R.Lean.UInt8.lit(76), Con{R.Lean.UInt8.lit(77), Con{R.Lean.UInt8.lit(0), Con{R.Lean.UInt8.lit(1), Nil{}}}}}}}

law banner.decoded:
  {banner() == banner.bytes() : R.Lean.ByteArray}

def banner.decoded():
  {==}

def Recognizes(+glyph: Models_Glyphs.Glyph, +digit: Nat) -> Data:
  {digit == Models_Glyphs.digitOf(glyph) : Nat}

def recognizesCheck(+glyph: Models_Glyphs.Glyph, +digit: Nat) -> Bool:
  L.Lean.Nat.beq(digit, Models_Glyphs.digitOf(glyph))

law recognizes_check_sound:
  for +glyph: Models_Glyphs.Glyph
  for +digit: Nat
  for +ll_h0: {recognizesCheck(glyph, digit) == True{} : Bool}
  Recognizes(glyph, digit)

def recognizes_check_sound(glyph, digit, ll_h0):
  LA.sound(Con{digit, Con{Models_Glyphs.digitOf(glyph), Nil{}}}, LA.FEq{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BEq{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Nil{}}, 9n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{1n, Nil{}}}}}, LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}}, {==}, (ll_h0, Unit{}))

law recognizes_check_complete:
  for +glyph: Models_Glyphs.Glyph
  for +digit: Nat
  for +ll_h0: Recognizes(glyph, digit)
  {recognizesCheck(glyph, digit) == True{} : Bool}

def recognizes_check_complete(glyph, digit, ll_h0):
  LA.sound(Con{digit, Con{Models_Glyphs.digitOf(glyph), Nil{}}}, LA.FIs{LA.BEq{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Con{LA.FEq{LA.TVar{0n}, LA.TVar{1n}}, Nil{}}, 11n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{1n, Nil{}}}}}, LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}}, {==}, (ll_h0, Unit{}))

law DigitContract.postcondition_sound:
  R.LexLeanModels.Sound2(Models_Glyphs.Glyph, Nat, (+ll_x1 => +ll_x2 => recognizesCheck(ll_x1, ll_x2)), (+ll_x3 => +ll_x4 => Recognizes(ll_x3, ll_x4)))

def DigitContract.postcondition_sound():
  ll_a5 => ll_a6 => ll_a7 => recognizes_check_sound(ll_a5, ll_a6, ll_a7)

law DigitContract.postcondition_complete:
  R.LexLeanModels.Complete2(Models_Glyphs.Glyph, Nat, (+ll_x8 => +ll_x9 => recognizesCheck(ll_x8, ll_x9)), (+ll_x10 => +ll_x11 => Recognizes(ll_x10, ll_x11)))

def DigitContract.postcondition_complete():
  ll_a12 => ll_a13 => ll_a14 => recognizes_check_complete(ll_a12, ll_a13, ll_a14)

law digit_net_width:
  for +glyph: Models_Glyphs.Glyph
  {R.LexLeanRuntime.length.List(L.Lean.Int, Models_Glyphs.encode(glyph)) == 7n : Nat}

def digit_net_width(glyph):
  Models_Glyphs.encode_width(glyph)

def DigitNet.encoded(+glyph: Models_Glyphs.Glyph) -> List<&2, L.Lean.Int>:
  Models_Glyphs.encode(glyph)

def ll_match17(+ll_v18: List<&2, L.Lean.Int>, +__sum: L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), +__weight: L.Lean.Int) -> L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>):
  match ll_v18:
    case Nil{}:
      __sum
    case Con{__value, __rest}:
      (L.Lean.Int.sub(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, __sum), L.Lean.Int.neg(L.Lean.Int.mul(__weight, __value))), __rest)

def ll_match15(+ll_v16: List<&2, L.Lean.Int>, +__acc: L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), +__row: List<&2, L.Lean.Int>, +__values: List<&2, L.Lean.Int>) -> L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>):
  match ll_v16:
    case Nil{}:
      __acc
    case Con{__bias, __biases}:
      (R.LexLeanRuntime.append.List(L.Lean.Int, S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), Con{L.Lean.Int.sub(__bias, L.Lean.Int.neg(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, S.Sem.listFold(~L.Lean.Int, ~L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), ~Unit, ~(+ll_e => +__sum => +__weight => ll_match17(S.Sem.snd(L.Lean.Int, List<&2, L.Lean.Int>, __sum), __sum, __weight)), Unit{}, __row, (L.ofNat{0n}, __values))))), Nil{}}), __biases)

def DigitNet.layer1(+__values: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, S.Sem.listFold(~List<&2, L.Lean.Int>, ~L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), ~List<&2, L.Lean.Int>, ~(+ll_e => +__acc => +__row => (
    +__values = ll_e
    ll_match15(S.Sem.snd(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), __acc, __row, __values)
  )), __values, hiddenWeights(), (Nil{}, hiddenBias())))

def DigitNet.layer2(+__values: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  S.Sem.listFold(~L.Lean.Int, ~List<&2, L.Lean.Int>, ~Unit, ~(+ll_e => +__out => +__value => R.LexLeanRuntime.append.List(L.Lean.Int, __out, Con{S.Sem.ite(L.Lean.Int, R.LexLeanCollections.lessThan.Int(__value, L.ofNat{0n}), L.ofNat{0n}, __value), Nil{}})), Unit{}, __values, Nil{})

def DigitNet.layer3(+__values: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  S.Sem.listFold(~L.Lean.Int, ~List<&2, L.Lean.Int>, ~Unit, ~(+ll_e => +__out => +__value => R.LexLeanRuntime.append.List(L.Lean.Int, __out, Con{(
    +__quotient = R.LexLeanRuntime.quotient.Int(__value, L.ofNat{4n}, L.ofNat{0n})
    S.Sem.ite(L.Lean.Int, R.LexLeanCollections.lessThan.Int(__quotient, L.ofNat{0n}), L.ofNat{0n}, S.Sem.ite(L.Lean.Int, R.LexLeanCollections.lessThan.Int(L.ofNat{127n}, __quotient), L.ofNat{127n}, __quotient))
  ), Nil{}})), Unit{}, __values, Nil{})

def ll_match21(+ll_v22: List<&2, L.Lean.Int>, +__sum: L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), +__weight: L.Lean.Int) -> L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>):
  match ll_v22:
    case Nil{}:
      __sum
    case Con{__value, __rest}:
      (L.Lean.Int.sub(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, __sum), L.Lean.Int.neg(L.Lean.Int.mul(__weight, __value))), __rest)

def ll_match19(+ll_v20: List<&2, L.Lean.Int>, +__acc: L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), +__row: List<&2, L.Lean.Int>, +__values: List<&2, L.Lean.Int>) -> L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>):
  match ll_v20:
    case Nil{}:
      __acc
    case Con{__bias, __biases}:
      (R.LexLeanRuntime.append.List(L.Lean.Int, S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), Con{L.Lean.Int.sub(__bias, L.Lean.Int.neg(S.Sem.fst(L.Lean.Int, List<&2, L.Lean.Int>, S.Sem.listFold(~L.Lean.Int, ~L.Lean.Prod(L.Lean.Int, List<&2, L.Lean.Int>), ~Unit, ~(+ll_e => +__sum => +__weight => ll_match21(S.Sem.snd(L.Lean.Int, List<&2, L.Lean.Int>, __sum), __sum, __weight)), Unit{}, __row, (L.ofNat{0n}, __values))))), Nil{}}), __biases)

def DigitNet.layer4(+__values: List<&2, L.Lean.Int>) -> List<&2, L.Lean.Int>:
  S.Sem.fst(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, S.Sem.listFold(~List<&2, L.Lean.Int>, ~L.Lean.Prod(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>), ~List<&2, L.Lean.Int>, ~(+ll_e => +__acc => +__row => (
    +__values = ll_e
    ll_match19(S.Sem.snd(List<&2, L.Lean.Int>, List<&2, L.Lean.Int>, __acc), __acc, __row, __values)
  )), __values, outputWeights(), (Nil{}, outputBias())))

def DigitNet.logits(+glyph: Models_Glyphs.Glyph) -> List<&2, L.Lean.Int>:
  DigitNet.layer4(DigitNet.layer3(DigitNet.layer2(DigitNet.layer1(DigitNet.encoded(glyph)))))

def ll_match23(+ll_v24: Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>) -> Nat:
  match ll_v24:
    case None{}:
      0n
    case Some{__winner}:
      S.Sem.fst(Nat, L.Lean.Int, __winner)

def ll_match27(+ll_v28: Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, +__label: Nat, +__score: L.Lean.Int) -> Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>:
  match ll_v28:
    case None{}:
      Some{(__label, __score)}
    case Some{__leader}:
      S.Sem.ite(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, R.LexLeanCollections.lessThan.Int(S.Sem.snd(Nat, L.Lean.Int, __leader), __score), Some{(__label, __score)}, Some{__leader})

def ll_match25(+ll_v26: List<&2, Nat>, +__best: L.Lean.Prod(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>), +__score: L.Lean.Int) -> L.Lean.Prod(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>):
  match ll_v26:
    case Nil{}:
      __best
    case Con{__label, __labels}:
      (ll_match27(S.Sem.fst(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>, __best), __label, __score), __labels)

def DigitNet(+glyph: Models_Glyphs.Glyph) -> Nat:
  ll_match23(S.Sem.fst(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>, S.Sem.listFold(~L.Lean.Int, ~L.Lean.Prod(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>), ~Unit, ~(+ll_e => +__best => +__score => ll_match25(S.Sem.snd(Maybe<&2, L.Lean.Prod(Nat, L.Lean.Int)>, List<&2, Nat>, __best), __best, __score)), Unit{}, DigitNet.logits(glyph), (None{}, Con{0n, Con{1n, Con{2n, Con{3n, Con{4n, Con{5n, Con{6n, Con{7n, Con{8n, Con{9n, Nil{}}}}}}}}}}}))))

law digit_net_exact:
  for +glyph: Models_Glyphs.Glyph
  {DigitNet(glyph) == Models_Glyphs.digitOf(glyph) : Nat}

def digit_net_exact(glyph):
  match glyph:
    case Models_Glyphs.Glyph.g0{}:
      {==}
    case Models_Glyphs.Glyph.g1{}:
      {==}
    case Models_Glyphs.Glyph.g2{}:
      {==}
    case Models_Glyphs.Glyph.g3{}:
      {==}
    case Models_Glyphs.Glyph.g4{}:
      {==}
    case Models_Glyphs.Glyph.g5{}:
      {==}
    case Models_Glyphs.Glyph.g6{}:
      {==}
    case Models_Glyphs.Glyph.g7{}:
      {==}
    case Models_Glyphs.Glyph.g8{}:
      {==}
    case Models_Glyphs.Glyph.g9{}:
      {==}

law digit_net_correct:
  for +glyph: Models_Glyphs.Glyph
  Recognizes(glyph, DigitNet(glyph))

def digit_net_correct(glyph):
  match glyph:
    case Models_Glyphs.Glyph.g0{}:
      {==}
    case Models_Glyphs.Glyph.g1{}:
      {==}
    case Models_Glyphs.Glyph.g2{}:
      {==}
    case Models_Glyphs.Glyph.g3{}:
      {==}
    case Models_Glyphs.Glyph.g4{}:
      {==}
    case Models_Glyphs.Glyph.g5{}:
      {==}
    case Models_Glyphs.Glyph.g6{}:
      {==}
    case Models_Glyphs.Glyph.g7{}:
      {==}
    case Models_Glyphs.Glyph.g8{}:
      {==}
    case Models_Glyphs.Glyph.g9{}:
      {==}

def labeledGlyphs() -> List<&2, L.Lean.Prod(Models_Glyphs.Glyph, Nat)>:
  Con{(Models_Glyphs.Glyph.g3{}, 3n), Con{(Models_Glyphs.Glyph.g0{}, 0n), Con{(Models_Glyphs.Glyph.g7{}, 7n), Con{(Models_Glyphs.Glyph.g4{}, 4n), Con{(Models_Glyphs.Glyph.g1{}, 1n), Con{(Models_Glyphs.Glyph.g8{}, 8n), Con{(Models_Glyphs.Glyph.g5{}, 5n), Con{(Models_Glyphs.Glyph.g2{}, 1n), Con{(Models_Glyphs.Glyph.g9{}, 9n), Con{(Models_Glyphs.Glyph.g6{}, 6n), Con{(Models_Glyphs.Glyph.g3{}, 3n), Con{(Models_Glyphs.Glyph.g0{}, 0n), Con{(Models_Glyphs.Glyph.g7{}, 7n), Con{(Models_Glyphs.Glyph.g4{}, 4n), Con{(Models_Glyphs.Glyph.g1{}, 1n), Con{(Models_Glyphs.Glyph.g8{}, 8n), Con{(Models_Glyphs.Glyph.g5{}, 5n), Con{(Models_Glyphs.Glyph.g2{}, 2n), Con{(Models_Glyphs.Glyph.g9{}, 9n), Con{(Models_Glyphs.Glyph.g6{}, 7n), Con{(Models_Glyphs.Glyph.g3{}, 3n), Con{(Models_Glyphs.Glyph.g0{}, 0n), Con{(Models_Glyphs.Glyph.g7{}, 7n), Con{(Models_Glyphs.Glyph.g4{}, 4n), Con{(Models_Glyphs.Glyph.g1{}, 1n), Con{(Models_Glyphs.Glyph.g8{}, 8n), Con{(Models_Glyphs.Glyph.g5{}, 5n), Con{(Models_Glyphs.Glyph.g2{}, 2n), Con{(Models_Glyphs.Glyph.g9{}, 9n), Con{(Models_Glyphs.Glyph.g6{}, 6n), Con{(Models_Glyphs.Glyph.g3{}, 3n), Con{(Models_Glyphs.Glyph.g0{}, 0n), Con{(Models_Glyphs.Glyph.g7{}, 7n), Con{(Models_Glyphs.Glyph.g4{}, 8n), Con{(Models_Glyphs.Glyph.g1{}, 1n), Con{(Models_Glyphs.Glyph.g8{}, 8n), Con{(Models_Glyphs.Glyph.g5{}, 5n), Con{(Models_Glyphs.Glyph.g2{}, 2n), Con{(Models_Glyphs.Glyph.g9{}, 9n), Con{(Models_Glyphs.Glyph.g6{}, 6n), Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def sameDigit(+expected: Nat, +observed: Nat) -> Bool:
  L.Lean.Nat.beq(expected, observed)

law same_digit_sound:
  for +expected: Nat
  for +observed: Nat
  for +ll_h0: {sameDigit(expected, observed) == True{} : Bool}
  {expected == observed : Nat}

def same_digit_sound(expected, observed, ll_h0):
  LA.sound(Con{expected, Con{observed, Nil{}}}, LA.FEq{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BEq{LA.TVar{0n}, LA.TVar{1n}}, True{}}, Nil{}}, 9n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{1n, Nil{}}}}}, LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}}, {==}, (ll_h0, Unit{}))

law labeled_agreement:
  L.Lean.Prod({R.LexLeanRuntime.length.List(L.Lean.Prod(Models_Glyphs.Glyph, Nat), labeledGlyphs()) == 40n : Nat}, {S.Sem.listFold(~L.Lean.Prod(Models_Glyphs.Glyph, Nat), ~Nat, ~Unit, ~(+ll_e => +count => +example => S.Sem.ite(Nat, sameDigit(DigitNet(S.Sem.fst(Models_Glyphs.Glyph, Nat, example)), S.Sem.snd(Models_Glyphs.Glyph, Nat, example)), L.Lean.Nat.add(count, 1n), count)), Unit{}, labeledGlyphs(), 0n) == 37n : Nat})

def labeled_agreement():
  ({==}, {==})

law DigitEvidence.labeled_agreement:
  R.LexLeanModels.Agreement(Models_Glyphs.Glyph, Nat, (+ll_x29 => DigitNet(ll_x29)), (+ll_x30 => +ll_x31 => sameDigit(ll_x30, ll_x31)), labeledGlyphs(), 40n, 37n)

def DigitEvidence.labeled_agreement():
  ({==}, {==})

law DigitEvidence.digit_net_exact:
  R.LexLeanModels.EquivalentTotal(Models_Glyphs.Glyph, Nat, (+ll_x32 => DigitNet(ll_x32)), (+ll_x33 => Models_Glyphs.digitOf(ll_x33)))

def DigitEvidence.digit_net_exact():
  ll_a34 => digit_net_exact(ll_a34)

law DigitEvidence.digit_net_correct:
  R.LexLeanModels.SatisfiesTotal(Models_Glyphs.Glyph, Nat, (+ll_x35 => +ll_x36 => Recognizes(ll_x35, ll_x36)), (+ll_x37 => DigitNet(ll_x37)))

def DigitEvidence.digit_net_correct():
  ll_a38 => digit_net_correct(ll_a38)

def DigitModel(+__input: Models_Glyphs.Glyph) -> Nat:
  DigitNet(__input)

def RawDigitModel(+__input: Models_Glyphs.Glyph) -> Nat:
  DigitNet(__input)

def digitName(+digit: Nat) -> Maybe<&2, String>:
  R.LexLeanRuntime.index.List(String, digitNames(), digit)
