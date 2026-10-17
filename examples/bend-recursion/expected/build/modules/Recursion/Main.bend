import Base
import ../LexLeanPrelude.bend as L
import ../LexLeanSemantic.bend as S
import ../LexLeanLinArith.bend as LA
import ./Syntax.bend as Recursion_Syntax

def forestSize(~Item: Data, +forest: List<&2, Recursion_Syntax.Rose<Item>>) -> Nat:
  match forest:
    case Nil{}:
      0n
    case Con{head, tail}:
      match head:
        case Recursion_Syntax.Rose.node{label, children}:
          L.Lean.Nat.add(L.Lean.Nat.add(1n, forestSize(~Item, children)), forestSize(~Item, tail))

def roseSize(~Item: Data, +rose: Recursion_Syntax.Rose<Item>) -> Nat:
  match rose:
    case Recursion_Syntax.Rose.node{label, children}:
      L.Lean.Nat.add(1n, forestSize(~Item, children))

def isEven(+number: Nat) -> Bool:
  match number:
    case 0n:
      True{}
    case 1n+previous:
      match previous:
        case 0n:
          False{}
        case 1n+previous:
          isEven(previous)

def isOdd(+number: Nat) -> Bool:
  match number:
    case 0n:
      False{}
    case 1n+previous:
      isEven(previous)

law countdown_decreases:
  for +number: Nat
  for +steps: Nat
  for +ll_h0: {L.Lean.Nat.blt(number, 2n) == False{} : Bool}
  S.Sem.lt(L.Lean.Nat.sub(number, 2n), number)

def countdown_decreases(number, steps, ll_h0):
  LA.sound(Con{L.Lean.Nat.sub(number, 2n), Con{number, Nil{}}}, LA.FLt{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BLt{LA.TVar{1n}, LA.TLit{2n}}, False{}}, Con{LA.FSub{LA.TVar{0n}, LA.TVar{1n}, LA.TLit{2n}}, Nil{}}}, 15n, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}, {==}, (ll_h0, ({==}, Unit{})))

def countdown.ll_go(+ll_fuel1: Nat, +number: Nat, +steps: Nat, +ll_bound3: S.Sem.lt(number, ll_fuel1)) -> Nat:
  match ll_fuel1:
    case 0n:
      S.Sem.lt_zero(Nat, number, ll_bound3)
    case 1n+ll_fuel2:
      S.Sem.iteDep(Nat, L.Lean.Nat.blt(number, 2n), (+ll_w4 => (
        steps
      )), (+ll_w5 => (
        countdown.ll_go(ll_fuel2, L.Lean.Nat.sub(number, 2n), L.Lean.Nat.add(steps, 1n), S.Sem.lt_fuel(L.Lean.Nat.sub(number, 2n), number, ll_fuel2, countdown_decreases(number, steps, ll_w5), ll_bound3))
      )))

def countdown(+number: Nat, +steps: Nat) -> Nat:
  countdown.ll_go(1n+number, number, steps, S.Sem.lt_succ(number))

law reduce_decreases:
  for +value: Nat
  for +bound: Nat
  for +ll_h0: {L.Lean.Nat.beq(bound, 0n) == False{} : Bool}
  for +ll_h1: {L.Lean.Nat.blt(value, bound) == False{} : Bool}
  S.Sem.lt(L.Lean.Nat.sub(value, bound), value)

def reduce_decreases(value, bound, ll_h0, ll_h1):
  LA.sound(Con{L.Lean.Nat.sub(value, bound), Con{value, Con{bound, Nil{}}}}, LA.FLt{LA.TVar{0n}, LA.TVar{1n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{2n}}, Con{LA.FIs{LA.BEq{LA.TVar{2n}, LA.TLit{0n}}, False{}}, Con{LA.FIs{LA.BLt{LA.TVar{1n}, LA.TVar{2n}}, False{}}, Con{LA.FSub{LA.TVar{0n}, LA.TVar{1n}, LA.TVar{2n}}, Nil{}}}}}, 25n, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{1n, Nil{}}}}}, LA.Fork{LA.Leaf{Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Con{0n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}, {==}, ({==}, (ll_h0, (ll_h1, ({==}, Unit{})))))

def reduce.ll_go(+ll_fuel6: Nat, +value: Nat, +bound: Nat, +ll_bound8: S.Sem.lt(value, ll_fuel6)) -> Nat:
  match ll_fuel6:
    case 0n:
      S.Sem.lt_zero(Nat, value, ll_bound8)
    case 1n+ll_fuel7:
      S.Sem.iteDep(Nat, L.Lean.Nat.beq(bound, 0n), (+ll_w9 => (
        value
      )), (+ll_w10 => (
        S.Sem.iteDep(Nat, L.Lean.Nat.blt(value, bound), (+ll_w11 => (
          value
        )), (+ll_w12 => (
          reduce.ll_go(ll_fuel7, L.Lean.Nat.sub(value, bound), bound, S.Sem.lt_fuel(L.Lean.Nat.sub(value, bound), value, ll_fuel7, reduce_decreases(value, bound, ll_w10, ll_w12), ll_bound8))
        )))
      )))

def reduce(+value: Nat, +bound: Nat) -> Nat:
  reduce.ll_go(1n+value, value, bound, S.Sem.lt_succ(value))

law search_decreases:
  for +target: Nat
  for +low: Nat
  for +high: Nat
  for +ll_h0: {L.Lean.Nat.blt(low, high) == True{} : Bool}
  for +ll_h1: {L.Lean.Nat.ble(target, L.Lean.Nat.add(low, low)) == False{} : Bool}
  S.Sem.lt(L.Lean.Nat.sub(high, L.Lean.Nat.add(low, 1n)), L.Lean.Nat.sub(high, low))

def search_decreases(target, low, high, ll_h0, ll_h1):
  LA.sound(Con{L.Lean.Nat.sub(high, L.Lean.Nat.add(low, 1n)), Con{high, Con{low, Con{L.Lean.Nat.sub(high, low), Con{target, Nil{}}}}}}, LA.FLt{LA.TVar{0n}, LA.TVar{3n}}, Con{LA.FIs{LA.BLt{LA.TVar{2n}, LA.TVar{1n}}, True{}}, Con{LA.FSub{LA.TVar{0n}, LA.TVar{1n}, LA.TAdd{LA.TVar{2n}, LA.TLit{1n}}}, Con{LA.FSub{LA.TVar{3n}, LA.TVar{1n}, LA.TVar{2n}}, Nil{}}}}, 23n, LA.Fork{LA.Fork{LA.Leaf{Con{1n, Con{0n, Con{0n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}, {==}, (ll_h0, ({==}, ({==}, Unit{}))))

def search.ll_go(+ll_fuel13: Nat, +target: Nat, +low: Nat, +high: Nat, +ll_bound15: S.Sem.lt(L.Lean.Nat.sub(high, low), ll_fuel13)) -> Nat:
  match ll_fuel13:
    case 0n:
      S.Sem.lt_zero(Nat, L.Lean.Nat.sub(high, low), ll_bound15)
    case 1n+ll_fuel14:
      S.Sem.iteDep(Nat, L.Lean.Nat.blt(low, high), (+ll_w16 => (
        S.Sem.iteDep(Nat, L.Lean.Nat.ble(target, L.Lean.Nat.add(low, low)), (+ll_w17 => (
          low
        )), (+ll_w18 => (
          search.ll_go(ll_fuel14, target, L.Lean.Nat.add(low, 1n), high, S.Sem.lt_fuel(L.Lean.Nat.sub(high, L.Lean.Nat.add(low, 1n)), L.Lean.Nat.sub(high, low), ll_fuel14, search_decreases(target, low, high, ll_w16, ll_w18), ll_bound15))
        )))
      )), (+ll_w19 => (
        high
      )))

def search(+target: Nat, +low: Nat, +high: Nat) -> Nat:
  search.ll_go(1n+L.Lean.Nat.sub(high, low), target, low, high, S.Sem.lt_succ(L.Lean.Nat.sub(high, low)))

law rose_size:
  {roseSize(~Nat, Recursion_Syntax.Rose.node{1n, Con{Recursion_Syntax.Rose.node{2n, Nil{}}, Con{Recursion_Syntax.Rose.node{3n, Nil{}}, Nil{}}}}) == 3n : Nat}

def rose_size():
  {==}

law ten_is_even:
  {isEven(10n) == True{} : Bool}

def ten_is_even():
  {==}

law countdown_nine:
  {countdown(9n, 0n) == 4n : Nat}

def countdown_nine():
  {==}

law reduce_twenty_three:
  {reduce(23n, 5n) == 3n : Nat}

def reduce_twenty_three():
  {==}

law search_first:
  {search(7n, 0n, 10n) == 4n : Nat}

def search_first():
  {==}

def weight(+term: Recursion_Syntax.Term) -> Nat:
  match term:
    case Recursion_Syntax.Term.literal{value}:
      1n
    case Recursion_Syntax.Term.plus{left, right}:
      L.Lean.Nat.add(L.Lean.Nat.add(L.Lean.Nat.add(weight(left), weight(left)), weight(right)), 1n)

law reassociate_literal:
  for +term: Recursion_Syntax.Term
  for +left: Recursion_Syntax.Term
  for +right: Recursion_Syntax.Term
  for +value: Nat
  for +ll_h0: {term == Recursion_Syntax.Term.plus{left, right} : Recursion_Syntax.Term}
  for +ll_h1: {left == Recursion_Syntax.Term.literal{value} : Recursion_Syntax.Term}
  S.Sem.lt(weight(right), weight(term))

def reassociate_literal(term, left, right, value, ll_h0, ll_h1):
  %Equal.sym(Recursion_Syntax.Term, term, Recursion_Syntax.Term.plus{left, right}, ll_h0) : S.Sem.lt(weight(right), weight(_))
  %Equal.sym(Recursion_Syntax.Term, left, Recursion_Syntax.Term.literal{value}, ll_h1) : S.Sem.lt(weight(right), weight(Recursion_Syntax.Term.plus{_, right}))
  LA.sound(Con{weight(right), Nil{}}, LA.FLt{LA.TVar{0n}, LA.TAdd{LA.TAdd{LA.TLit{2n}, LA.TVar{0n}}, LA.TLit{1n}}}, Nil{}, 3n, LA.Leaf{Con{1n, Nil{}}}, {==}, Unit{})

law reassociate_plus:
  for +term: Recursion_Syntax.Term
  for +left: Recursion_Syntax.Term
  for +right: Recursion_Syntax.Term
  for +inner: Recursion_Syntax.Term
  for +rest: Recursion_Syntax.Term
  for +ll_h0: {term == Recursion_Syntax.Term.plus{left, right} : Recursion_Syntax.Term}
  for +ll_h1: {left == Recursion_Syntax.Term.plus{inner, rest} : Recursion_Syntax.Term}
  S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}), weight(term))

def reassociate_plus(term, left, right, inner, rest, ll_h0, ll_h1):
  %Equal.sym(Recursion_Syntax.Term, term, Recursion_Syntax.Term.plus{left, right}, ll_h0) : S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}), weight(_))
  %Equal.sym(Recursion_Syntax.Term, left, Recursion_Syntax.Term.plus{inner, rest}, ll_h1) : S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}), weight(Recursion_Syntax.Term.plus{_, right}))
  LA.sound(Con{weight(inner), Con{weight(rest), Con{weight(right), Nil{}}}}, LA.FLt{LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{1n}, LA.TVar{1n}}, LA.TVar{2n}}, LA.TLit{1n}}}, LA.TLit{1n}}, LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TVar{1n}}, LA.TLit{1n}}, LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TVar{1n}}, LA.TLit{1n}}}, LA.TVar{2n}}, LA.TLit{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{0n}}, Nil{}}, 5n, LA.Leaf{Con{2n, Con{1n, Nil{}}}}, {==}, ({==}, Unit{}))

def reassociate.ll_go(+ll_fuel20: Nat, +term: Recursion_Syntax.Term, +ll_bound22: S.Sem.lt(weight(term), ll_fuel20)) -> Recursion_Syntax.Term:
  match ll_fuel20:
    case 0n:
      S.Sem.lt_zero(Recursion_Syntax.Term, weight(term), ll_bound22)
    case 1n+ll_fuel21:
      match term:
        case Recursion_Syntax.Term.literal{value}:
          Recursion_Syntax.Term.literal{value}
        case Recursion_Syntax.Term.plus{left, right}:
          match left:
            case Recursion_Syntax.Term.literal{value}:
              Recursion_Syntax.Term.plus{Recursion_Syntax.Term.literal{value}, reassociate.ll_go(ll_fuel21, right, S.Sem.lt_fuel(weight(right), weight(term), ll_fuel21, reassociate_literal(term, left, right, value, {==}, {==}), ll_bound22))}
            case Recursion_Syntax.Term.plus{inner, rest}:
              reassociate.ll_go(ll_fuel21, Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}, S.Sem.lt_fuel(weight(Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}), weight(term), ll_fuel21, reassociate_plus(term, left, right, inner, rest, {==}, {==}), ll_bound22))

def reassociate(+term: Recursion_Syntax.Term) -> Recursion_Syntax.Term:
  reassociate.ll_go(1n+weight(term), term, S.Sem.lt_succ(weight(term)))

law reassociate_weight:
  {weight(reassociate(Recursion_Syntax.Term.plus{Recursion_Syntax.Term.plus{Recursion_Syntax.Term.literal{1n}, Recursion_Syntax.Term.literal{2n}}, Recursion_Syntax.Term.literal{3n}})) == 7n : Nat}

def reassociate_weight():
  {==}

law prune_plus:
  for +term: Recursion_Syntax.Term
  for +left: Recursion_Syntax.Term
  for +right: Recursion_Syntax.Term
  for +inner: Recursion_Syntax.Term
  for +rest: Recursion_Syntax.Term
  for +ll_h0: {term == Recursion_Syntax.Term.plus{left, right} : Recursion_Syntax.Term}
  for +ll_h1: {left == Recursion_Syntax.Term.plus{inner, rest} : Recursion_Syntax.Term}
  S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, right}), weight(term))

def prune_plus(term, left, right, inner, rest, ll_h0, ll_h1):
  %Equal.sym(Recursion_Syntax.Term, term, Recursion_Syntax.Term.plus{left, right}, ll_h0) : S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, right}), weight(_))
  %Equal.sym(Recursion_Syntax.Term, left, Recursion_Syntax.Term.plus{inner, rest}, ll_h1) : S.Sem.lt(weight(Recursion_Syntax.Term.plus{inner, right}), weight(Recursion_Syntax.Term.plus{_, right}))
  LA.sound(Con{weight(inner), Con{weight(right), Con{weight(rest), Nil{}}}}, LA.FLt{LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TVar{1n}}, LA.TLit{1n}}, LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TVar{2n}}, LA.TLit{1n}}, LA.TAdd{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TVar{2n}}, LA.TLit{1n}}}, LA.TVar{1n}}, LA.TLit{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{0n}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{2n}}, Nil{}}}, 7n, LA.Leaf{Con{2n, Con{2n, Con{1n, Nil{}}}}}, {==}, ({==}, ({==}, Unit{})))

def prune.ll_go(+ll_fuel23: Nat, +term: Recursion_Syntax.Term, +ll_bound25: S.Sem.lt(weight(term), ll_fuel23)) -> Recursion_Syntax.Term:
  match ll_fuel23:
    case 0n:
      S.Sem.lt_zero(Recursion_Syntax.Term, weight(term), ll_bound25)
    case 1n+ll_fuel24:
      match term:
        case Recursion_Syntax.Term.literal{value}:
          Recursion_Syntax.Term.literal{value}
        case Recursion_Syntax.Term.plus{left, right}:
          match left:
            case Recursion_Syntax.Term.literal{value}:
              prune.ll_go(ll_fuel24, right, S.Sem.lt_fuel(weight(right), weight(term), ll_fuel24, reassociate_literal(term, left, right, value, {==}, {==}), ll_bound25))
            case Recursion_Syntax.Term.plus{inner, rest}:
              prune.ll_go(ll_fuel24, Recursion_Syntax.Term.plus{inner, right}, S.Sem.lt_fuel(weight(Recursion_Syntax.Term.plus{inner, right}), weight(term), ll_fuel24, prune_plus(term, left, right, inner, rest, {==}, {==}), ll_bound25))

def prune(+term: Recursion_Syntax.Term) -> Recursion_Syntax.Term:
  prune.ll_go(1n+weight(term), term, S.Sem.lt_succ(weight(term)))

law prune_result:
  {weight(prune(Recursion_Syntax.Term.plus{Recursion_Syntax.Term.plus{Recursion_Syntax.Term.literal{1n}, Recursion_Syntax.Term.literal{2n}}, Recursion_Syntax.Term.literal{3n}})) == 1n : Nat}

def prune_result():
  {==}

law ping_to_pong:
  for +number: Nat
  for +ll_h0: {L.Lean.Nat.beq(number, 0n) == False{} : Bool}
  S.Sem.lt(L.Lean.Nat.add(number, number), L.Lean.Nat.add(L.Lean.Nat.add(number, number), 1n))

def ping_to_pong(number, ll_h0):
  LA.sound(Con{number, Nil{}}, LA.FLt{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TLit{1n}}}, Nil{}, 3n, LA.Leaf{Con{1n, Nil{}}}, {==}, Unit{})

law pong_to_ping:
  for +number: Nat
  for +ll_h0: {L.Lean.Nat.beq(number, 0n) == False{} : Bool}
  S.Sem.lt(L.Lean.Nat.add(L.Lean.Nat.add(L.Lean.Nat.sub(number, 1n), L.Lean.Nat.sub(number, 1n)), 1n), L.Lean.Nat.add(number, number))

def pong_to_ping(number, ll_h0):
  LA.sound(Con{L.Lean.Nat.sub(number, 1n), Con{number, Nil{}}}, LA.FLt{LA.TAdd{LA.TAdd{LA.TVar{0n}, LA.TVar{0n}}, LA.TLit{1n}}, LA.TAdd{LA.TVar{1n}, LA.TVar{1n}}}, Con{LA.FLe{LA.TLit{0n}, LA.TVar{1n}}, Con{LA.FIs{LA.BEq{LA.TVar{1n}, LA.TLit{0n}}, False{}}, Con{LA.FSub{LA.TVar{0n}, LA.TVar{1n}, LA.TLit{1n}}, Nil{}}}}, 21n, LA.Fork{LA.Leaf{Con{1n, Con{1n, Nil{}}}}, LA.Fork{LA.Leaf{Con{0n, Con{2n, Con{0n, Con{0n, Con{0n, Con{1n, Nil{}}}}}}}}, LA.Leaf{Con{0n, Con{0n, Con{1n, Con{1n, Nil{}}}}}}}}, {==}, ({==}, (ll_h0, ({==}, Unit{}))))
