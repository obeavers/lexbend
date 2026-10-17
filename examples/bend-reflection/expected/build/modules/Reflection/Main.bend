import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanLinArith.bend as LA

type ll.Pair is Data:
  ll.Pair.mk{left: Nat, right: Nat}

def ll.Pair.left(ll_record: ll.Pair) -> Nat:
  match ll_record:
    case ll.Pair.mk{ll_f0, ll_f1}:
      ll_f0

def ll.Pair.right(ll_record: ll.Pair) -> Nat:
  match ll_record:
    case ll.Pair.mk{ll_f0, ll_f1}:
      ll_f1

def validatePair(+pair: ll.Pair) -> Bool:
  L.Lean.Bool.and(L.Lean.Nat.beq(ll.Pair.left(pair), 0n), L.Lean.Nat.beq(ll.Pair.right(pair), 1n))

def PairValid(+pair: ll.Pair) -> Data:
  L.Lean.Prod({ll.Pair.left(pair) == 0n : Nat}, {ll.Pair.right(pair) == 1n : Nat})

law pair_reflects:
  for +pair: ll.Pair
  ({validatePair(pair) == True{} : Bool} -> PairValid(pair)) & (PairValid(pair) -> {validatePair(pair) == True{} : Bool})

def pair_reflects(pair):
  ((
    +ll_h0 => (
      (LA.sound(Con{ll.Pair.left(pair), Con{ll.Pair.right(pair), Nil{}}}, LA.FEq{LA.TVar{0n}, LA.TLit{0n}}, Con{LA.FIs{LA.BAnd{LA.BEq{LA.TVar{0n}, LA.TLit{0n}}, LA.BEq{LA.TVar{1n}, LA.TLit{1n}}}, True{}}, Nil{}}, 15n, LA.Fork{LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}, {==}, (ll_h0, Unit{})), LA.sound(Con{ll.Pair.right(pair), Con{ll.Pair.left(pair), Nil{}}}, LA.FEq{LA.TVar{0n}, LA.TLit{1n}}, Con{LA.FIs{LA.BAnd{LA.BEq{LA.TVar{1n}, LA.TLit{0n}}, LA.BEq{LA.TVar{0n}, LA.TLit{1n}}}, True{}}, Nil{}}, 15n, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}, {==}, (ll_h0, Unit{})))
    )
  ), (
    +ll_h0 => (
      LA.sound(Con{ll.Pair.left(pair), Con{ll.Pair.right(pair), Nil{}}}, LA.FIs{LA.BAnd{LA.BEq{LA.TVar{0n}, LA.TLit{0n}}, LA.BEq{LA.TVar{1n}, LA.TLit{1n}}}, True{}}, Con{LA.FAnd{LA.FEq{LA.TVar{0n}, LA.TLit{0n}}, LA.FEq{LA.TVar{1n}, LA.TLit{1n}}}, Nil{}}, 17n, LA.Fork{LA.Fork{LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}, LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}, LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, {==}, ((S.Sem.fst({ll.Pair.left(pair) == 0n : Nat}, {ll.Pair.right(pair) == 1n : Nat}, ll_h0), S.Sem.snd({ll.Pair.left(pair) == 0n : Nat}, {ll.Pair.right(pair) == 1n : Nat}, ll_h0)), Unit{}))
    )
  ))

def countsFrom(+values: List<&2, Nat>, +start: Nat) -> Bool:
  match values:
    case Nil{}:
      True{}
    case Con{head, tail}:
      L.Lean.Bool.and(L.Lean.Nat.beq(start, head), countsFrom(tail, L.Lean.Nat.add(start, 1n)))

def CountsFrom(+values: List<&2, Nat>, +start: Nat) -> Type:
  match values:
    case Nil{}:
      {0n == 0n : Nat}
    case Con{head, tail}:
      {start == head : Nat} & CountsFrom(tail, L.Lean.Nat.add(start, 1n))

def counts_reflects.ll_reflect1.forward(+ll_values: List<&2, Nat>, +ll_p: Nat, +ll_h: {countsFrom(ll_values, ll_p) == True{} : Bool}) -> CountsFrom(ll_values, ll_p):
  match ll_values:
    case Nil{}:
      {==}
    case Con{ll_v, ll_rest}:
      (S.Sem.beq_eq(ll_p, ll_v, S.Sem.and_left(L.Lean.Nat.beq(ll_p, ll_v), countsFrom(ll_rest, L.Lean.Nat.add(ll_p, 1n)), ll_h)), counts_reflects.ll_reflect1.forward(ll_rest, L.Lean.Nat.add(ll_p, 1n), S.Sem.and_right(L.Lean.Nat.beq(ll_p, ll_v), countsFrom(ll_rest, L.Lean.Nat.add(ll_p, 1n)), ll_h)))

def counts_reflects.ll_reflect1.backward(+ll_values: List<&2, Nat>, +ll_p: Nat, ll_h: CountsFrom(ll_values, ll_p)) -> {countsFrom(ll_values, ll_p) == True{} : Bool}:
  match ll_values:
    case Nil{}:
      {==}
    case Con{ll_v, ll_rest}:
      match ll_h:
        case (ll_hl, ll_hr):
          S.Sem.and_intro(L.Lean.Nat.beq(ll_p, ll_v), countsFrom(ll_rest, L.Lean.Nat.add(ll_p, 1n)), S.Sem.eq_beq(ll_p, ll_v, ll_hl), counts_reflects.ll_reflect1.backward(ll_rest, L.Lean.Nat.add(ll_p, 1n), ll_hr))

law counts_reflects:
  for +start: Nat
  for +values: List<&2, Nat>
  ({countsFrom(values, start) == True{} : Bool} -> CountsFrom(values, start)) & (CountsFrom(values, start) -> {countsFrom(values, start) == True{} : Bool})

def counts_reflects(start, values):
  ((+ll_reflected => counts_reflects.ll_reflect1.forward(values, start, ll_reflected)), (ll_reflected => counts_reflects.ll_reflect1.backward(values, start, ll_reflected)))

def allBelow(+values: List<&2, Nat>, +bound: Nat) -> Bool:
  match values:
    case Nil{}:
      True{}
    case Con{head, tail}:
      L.Lean.Bool.and(L.Lean.Nat.blt(head, bound), allBelow(tail, bound))

def AllBelow(+values: List<&2, Nat>, +bound: Nat) -> Type:
  match values:
    case Nil{}:
      {0n == 0n : Nat}
    case Con{head, tail}:
      S.Sem.lt(head, bound) & AllBelow(tail, bound)

def below_reflects.ll_reflect1.forward(+ll_values: List<&2, Nat>, +ll_p: Nat, +ll_h: {allBelow(ll_values, ll_p) == True{} : Bool}) -> AllBelow(ll_values, ll_p):
  match ll_values:
    case Nil{}:
      {==}
    case Con{ll_v, ll_rest}:
      (S.Sem.and_left(L.Lean.Nat.blt(ll_v, ll_p), allBelow(ll_rest, ll_p), ll_h), below_reflects.ll_reflect1.forward(ll_rest, ll_p, S.Sem.and_right(L.Lean.Nat.blt(ll_v, ll_p), allBelow(ll_rest, ll_p), ll_h)))

def below_reflects.ll_reflect1.backward(+ll_values: List<&2, Nat>, +ll_p: Nat, ll_h: AllBelow(ll_values, ll_p)) -> {allBelow(ll_values, ll_p) == True{} : Bool}:
  match ll_values:
    case Nil{}:
      {==}
    case Con{ll_v, ll_rest}:
      match ll_h:
        case (ll_hl, ll_hr):
          S.Sem.and_intro(L.Lean.Nat.blt(ll_v, ll_p), allBelow(ll_rest, ll_p), ll_hl, below_reflects.ll_reflect1.backward(ll_rest, ll_p, ll_hr))

law below_reflects:
  for +bound: Nat
  for +values: List<&2, Nat>
  ({allBelow(values, bound) == True{} : Bool} -> AllBelow(values, bound)) & (AllBelow(values, bound) -> {allBelow(values, bound) == True{} : Bool})

def below_reflects(bound, values):
  ((+ll_reflected => below_reflects.ll_reflect1.forward(values, bound, ll_reflected)), (ll_reflected => below_reflects.ll_reflect1.backward(values, bound, ll_reflected)))

law congruence_refl:
  for +value: Nat
  {L.Lean.Nat.add(value, 0n) == L.Lean.Nat.add(value, 0n) : Nat}

def congruence_refl(value):
  {==}

law congruence_unfolds:
  for +a: Nat
  {L.Lean.Nat.add(L.Lean.Nat.add(a, 0n), 3n) == L.Lean.Nat.add(a, 3n) : Nat}

def congruence_unfolds(a):
  {==}
