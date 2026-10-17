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

type exprSize.ll_sel<-ll_i: Recursion_Syntax.Expr.ll_index> is Data:
  exprSize.ll_sel.exprSize{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i0{} : Recursion_Syntax.Expr.ll_index}}
  exprSize.ll_sel.statementsSize{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i2{} : Recursion_Syntax.Expr.ll_index}}
  exprSize.ll_sel.statementSize{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i1{} : Recursion_Syntax.Expr.ll_index}}

def exprSize.ll_go(-ll_i: Recursion_Syntax.Expr.ll_index, +ll_x: Recursion_Syntax.Expr<ll_i>, +ll_s: exprSize.ll_sel<ll_i>) -> Nat:
  match ll_x:
    case Recursion_Syntax.Expr.literal{ll_f1, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          1n
        case exprSize.ll_sel.statementsSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.plus{ll_f2, ll_f3, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          L.Lean.Nat.add(L.Lean.Nat.add(exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f2, exprSize.ll_sel.exprSize{{==}}), exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f3, exprSize.ll_sel.exprSize{{==}})), 1n)
        case exprSize.ll_sel.statementsSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.block{ll_f4, ll_f5, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          L.Lean.Nat.add(exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, ll_f4, exprSize.ll_sel.statementsSize{{==}}), exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f5, exprSize.ll_sel.exprSize{{==}}))
        case exprSize.ll_sel.statementsSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Stmt.assign{ll_f6, ll_f7, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash1_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementsSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash1_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementSize{ll_es}:
          L.Lean.Nat.add(exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f7, exprSize.ll_sel.exprSize{{==}}), 1n)
    case Recursion_Syntax.Stmt.sequence{ll_f8, ll_f9, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash1_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementsSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash1_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementSize{ll_es}:
          L.Lean.Nat.add(exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f8, exprSize.ll_sel.statementSize{{==}}), exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f9, exprSize.ll_sel.statementSize{{==}}))
    case Recursion_Syntax.Expr.ll_nil2{ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash2_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementsSize{ll_es}:
          0n
        case exprSize.ll_sel.statementSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash2_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.ll_cons2{ll_f10, ll_f11, ll_ex}:
      match ll_s:
        case exprSize.ll_sel.exprSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash2_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
        case exprSize.ll_sel.statementsSize{ll_es}:
          L.Lean.Nat.add(exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f10, exprSize.ll_sel.statementSize{{==}}), exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, ll_f11, exprSize.ll_sel.statementsSize{{==}}))
        case exprSize.ll_sel.statementSize{ll_es}:
          Empty.absurd(Nat, Recursion_Syntax.Expr.ll_clash2_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))

def exprSize(+expression: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>) -> Nat:
  exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, expression, exprSize.ll_sel.exprSize{{==}})

def statementsSize(+statements: List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>) -> Nat:
  exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, Recursion_Syntax.Expr.ll_from2(statements), exprSize.ll_sel.statementsSize{{==}})

def statementSize(+statement: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>) -> Nat:
  exprSize.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, statement, exprSize.ll_sel.statementSize{{==}})

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

def countdown.ll_go(+ll_fuel12: Nat, +number: Nat, +steps: Nat, +ll_bound14: S.Sem.lt(number, ll_fuel12)) -> Nat:
  match ll_fuel12:
    case 0n:
      S.Sem.lt_zero(Nat, number, ll_bound14)
    case 1n+ll_fuel13:
      S.Sem.iteDep(Nat, L.Lean.Nat.blt(number, 2n), (+ll_w15 => (
        steps
      )), (+ll_w16 => (
        countdown.ll_go(ll_fuel13, L.Lean.Nat.sub(number, 2n), L.Lean.Nat.add(steps, 1n), S.Sem.lt_fuel(L.Lean.Nat.sub(number, 2n), number, ll_fuel13, countdown_decreases(number, steps, ll_w16), ll_bound14))
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

def reduce.ll_go(+ll_fuel17: Nat, +value: Nat, +bound: Nat, +ll_bound19: S.Sem.lt(value, ll_fuel17)) -> Nat:
  match ll_fuel17:
    case 0n:
      S.Sem.lt_zero(Nat, value, ll_bound19)
    case 1n+ll_fuel18:
      S.Sem.iteDep(Nat, L.Lean.Nat.beq(bound, 0n), (+ll_w20 => (
        value
      )), (+ll_w21 => (
        S.Sem.iteDep(Nat, L.Lean.Nat.blt(value, bound), (+ll_w22 => (
          value
        )), (+ll_w23 => (
          reduce.ll_go(ll_fuel18, L.Lean.Nat.sub(value, bound), bound, S.Sem.lt_fuel(L.Lean.Nat.sub(value, bound), value, ll_fuel18, reduce_decreases(value, bound, ll_w21, ll_w23), ll_bound19))
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

def search.ll_go(+ll_fuel24: Nat, +target: Nat, +low: Nat, +high: Nat, +ll_bound26: S.Sem.lt(L.Lean.Nat.sub(high, low), ll_fuel24)) -> Nat:
  match ll_fuel24:
    case 0n:
      S.Sem.lt_zero(Nat, L.Lean.Nat.sub(high, low), ll_bound26)
    case 1n+ll_fuel25:
      S.Sem.iteDep(Nat, L.Lean.Nat.blt(low, high), (+ll_w27 => (
        S.Sem.iteDep(Nat, L.Lean.Nat.ble(target, L.Lean.Nat.add(low, low)), (+ll_w28 => (
          low
        )), (+ll_w29 => (
          search.ll_go(ll_fuel25, target, L.Lean.Nat.add(low, 1n), high, S.Sem.lt_fuel(L.Lean.Nat.sub(high, L.Lean.Nat.add(low, 1n)), L.Lean.Nat.sub(high, low), ll_fuel25, search_decreases(target, low, high, ll_w27, ll_w29), ll_bound26))
        )))
      )), (+ll_w30 => (
        high
      )))

def search(+target: Nat, +low: Nat, +high: Nat) -> Nat:
  search.ll_go(1n+L.Lean.Nat.sub(high, low), target, low, high, S.Sem.lt_succ(L.Lean.Nat.sub(high, low)))

law rose_size:
  {roseSize(~Nat, Recursion_Syntax.Rose.node{1n, Con{Recursion_Syntax.Rose.node{2n, Nil{}}, Con{Recursion_Syntax.Rose.node{3n, Nil{}}, Nil{}}}}) == 3n : Nat}

def rose_size():
  {==}

law expression_size:
  {exprSize(Recursion_Syntax.Expr.block{Recursion_Syntax.Expr.ll_from2(Con{Recursion_Syntax.Stmt.assign{"x", Recursion_Syntax.Expr.literal{1n, {==}}, {==}}, Nil{}}), Recursion_Syntax.Expr.plus{Recursion_Syntax.Expr.literal{2n, {==}}, Recursion_Syntax.Expr.literal{3n, {==}}, {==}}, {==}}) == 5n : Nat}

def expression_size():
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

def reassociate.ll_go(+ll_fuel31: Nat, +term: Recursion_Syntax.Term, +ll_bound33: S.Sem.lt(weight(term), ll_fuel31)) -> Recursion_Syntax.Term:
  match ll_fuel31:
    case 0n:
      S.Sem.lt_zero(Recursion_Syntax.Term, weight(term), ll_bound33)
    case 1n+ll_fuel32:
      match term:
        case Recursion_Syntax.Term.literal{value}:
          Recursion_Syntax.Term.literal{value}
        case Recursion_Syntax.Term.plus{left, right}:
          match left:
            case Recursion_Syntax.Term.literal{value}:
              Recursion_Syntax.Term.plus{Recursion_Syntax.Term.literal{value}, reassociate.ll_go(ll_fuel32, right, S.Sem.lt_fuel(weight(right), weight(term), ll_fuel32, reassociate_literal(term, left, right, value, {==}, {==}), ll_bound33))}
            case Recursion_Syntax.Term.plus{inner, rest}:
              reassociate.ll_go(ll_fuel32, Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}, S.Sem.lt_fuel(weight(Recursion_Syntax.Term.plus{inner, Recursion_Syntax.Term.plus{rest, right}}), weight(term), ll_fuel32, reassociate_plus(term, left, right, inner, rest, {==}, {==}), ll_bound33))

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

def prune.ll_go(+ll_fuel34: Nat, +term: Recursion_Syntax.Term, +ll_bound36: S.Sem.lt(weight(term), ll_fuel34)) -> Recursion_Syntax.Term:
  match ll_fuel34:
    case 0n:
      S.Sem.lt_zero(Recursion_Syntax.Term, weight(term), ll_bound36)
    case 1n+ll_fuel35:
      match term:
        case Recursion_Syntax.Term.literal{value}:
          Recursion_Syntax.Term.literal{value}
        case Recursion_Syntax.Term.plus{left, right}:
          match left:
            case Recursion_Syntax.Term.literal{value}:
              prune.ll_go(ll_fuel35, right, S.Sem.lt_fuel(weight(right), weight(term), ll_fuel35, reassociate_literal(term, left, right, value, {==}, {==}), ll_bound36))
            case Recursion_Syntax.Term.plus{inner, rest}:
              prune.ll_go(ll_fuel35, Recursion_Syntax.Term.plus{inner, right}, S.Sem.lt_fuel(weight(Recursion_Syntax.Term.plus{inner, right}), weight(term), ll_fuel35, prune_plus(term, left, right, inner, rest, {==}, {==}), ll_bound36))

def prune(+term: Recursion_Syntax.Term) -> Recursion_Syntax.Term:
  prune.ll_go(1n+weight(term), term, S.Sem.lt_succ(weight(term)))

law prune_result:
  {weight(prune(Recursion_Syntax.Term.plus{Recursion_Syntax.Term.plus{Recursion_Syntax.Term.literal{1n}, Recursion_Syntax.Term.literal{2n}}, Recursion_Syntax.Term.literal{3n}})) == 1n : Nat}

def prune_result():
  {==}

type foldExpr.ll_sel<-ll_i: Recursion_Syntax.Expr.ll_index> is Data:
  foldExpr.ll_sel.foldExpr{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i0{} : Recursion_Syntax.Expr.ll_index}}
  foldExpr.ll_sel.foldStatements{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i2{} : Recursion_Syntax.Expr.ll_index}}
  foldExpr.ll_sel.foldStatement{ll_e: {ll_i == Recursion_Syntax.Expr.ll_index.i1{} : Recursion_Syntax.Expr.ll_index}}

def foldExpr.ll_out(-ll_i: Recursion_Syntax.Expr.ll_index, ll_s: foldExpr.ll_sel<ll_i>) -> Type:
  match ll_s:
    case foldExpr.ll_sel.foldExpr{_}:
      Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>
    case foldExpr.ll_sel.foldStatements{_}:
      List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>
    case foldExpr.ll_sel.foldStatement{_}:
      Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>

def ll_match42(+ll_v43: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, +foldedLeft: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, +foldedRight: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, +leftValue: Nat) -> Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>:
  match ll_v43:
    case Recursion_Syntax.Expr.literal{rightValue, _}:
      Recursion_Syntax.Expr.literal{L.Lean.Nat.add(leftValue, rightValue), {==}}
    case Recursion_Syntax.Expr.plus{rightFirst, rightSecond, _}:
      Recursion_Syntax.Expr.plus{foldedLeft, foldedRight, {==}}
    case Recursion_Syntax.Expr.block{rightStatements, rightResult, _}:
      Recursion_Syntax.Expr.plus{foldedLeft, foldedRight, {==}}
    case Recursion_Syntax.Stmt.assign{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_1(ll_e))
    case Recursion_Syntax.Stmt.sequence{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_1(ll_e))
    case Recursion_Syntax.Expr.ll_nil2{ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_2(ll_e))
    case Recursion_Syntax.Expr.ll_cons2{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_2(ll_e))

def ll_match40(+ll_v41: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, +foldedLeft: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, +foldedRight: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>) -> Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>:
  match ll_v41:
    case Recursion_Syntax.Expr.literal{leftValue, _}:
      ll_match42(foldedRight, foldedLeft, foldedRight, leftValue)
    case Recursion_Syntax.Expr.plus{leftFirst, leftSecond, _}:
      Recursion_Syntax.Expr.plus{foldedLeft, foldedRight, {==}}
    case Recursion_Syntax.Expr.block{leftStatements, leftResult, _}:
      Recursion_Syntax.Expr.plus{foldedLeft, foldedRight, {==}}
    case Recursion_Syntax.Stmt.assign{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_1(ll_e))
    case Recursion_Syntax.Stmt.sequence{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_1(ll_e))
    case Recursion_Syntax.Expr.ll_nil2{ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_2(ll_e))
    case Recursion_Syntax.Expr.ll_cons2{_, _, ll_e}:
      Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash0_2(ll_e))

def foldExpr.ll_go(-ll_i: Recursion_Syntax.Expr.ll_index, +ll_x: Recursion_Syntax.Expr<ll_i>, +ll_s: foldExpr.ll_sel<ll_i>) -> foldExpr.ll_out(ll_i, ll_s):
  match ll_x:
    case Recursion_Syntax.Expr.literal{ll_f37, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Recursion_Syntax.Expr.literal{ll_f37, {==}}
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Empty.absurd(List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.plus{ll_f38, ll_f39, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          +foldedLeft = {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f38, foldExpr.ll_sel.foldExpr{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>}
          +foldedRight = {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f39, foldExpr.ll_sel.foldExpr{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>}
          ll_match40(foldedLeft, foldedLeft, foldedRight)
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Empty.absurd(List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.block{ll_f44, ll_f45, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Recursion_Syntax.Expr.block{Recursion_Syntax.Expr.ll_from2({foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, ll_f44, foldExpr.ll_sel.foldStatements{{==}}) : List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>}), {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f45, foldExpr.ll_sel.foldExpr{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>}, {==}}
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Empty.absurd(List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>, Recursion_Syntax.Expr.ll_clash0_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>, Recursion_Syntax.Expr.ll_clash0_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i0{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, ll_ex), ll_es)))
    case Recursion_Syntax.Stmt.assign{ll_f46, ll_f47, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash1_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Empty.absurd(List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>, Recursion_Syntax.Expr.ll_clash1_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Recursion_Syntax.Stmt.assign{ll_f46, {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, ll_f47, foldExpr.ll_sel.foldExpr{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>}, {==}}
    case Recursion_Syntax.Stmt.sequence{ll_f48, ll_f49, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash1_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Empty.absurd(List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>, Recursion_Syntax.Expr.ll_clash1_2(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i1{}, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Recursion_Syntax.Stmt.sequence{{foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f48, foldExpr.ll_sel.foldStatement{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>}, {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f49, foldExpr.ll_sel.foldStatement{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>}, {==}}
    case Recursion_Syntax.Expr.ll_nil2{ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash2_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Nil{}
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>, Recursion_Syntax.Expr.ll_clash2_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
    case Recursion_Syntax.Expr.ll_cons2{ll_f50, ll_f51, ll_ex}:
      match ll_s:
        case foldExpr.ll_sel.foldExpr{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>, Recursion_Syntax.Expr.ll_clash2_0(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i0{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))
        case foldExpr.ll_sel.foldStatements{ll_es}:
          Con{{foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, ll_f50, foldExpr.ll_sel.foldStatement{{==}}) : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>}, {foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, ll_f51, foldExpr.ll_sel.foldStatements{{==}}) : List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>}}
        case foldExpr.ll_sel.foldStatement{ll_es}:
          Empty.absurd(Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>, Recursion_Syntax.Expr.ll_clash2_1(Equal.trans(Recursion_Syntax.Expr.ll_index, Recursion_Syntax.Expr.ll_index.i2{}, ll_i, Recursion_Syntax.Expr.ll_index.i1{}, Equal.sym(Recursion_Syntax.Expr.ll_index, ll_i, Recursion_Syntax.Expr.ll_index.i2{}, ll_ex), ll_es)))

def foldExpr(+expression: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>) -> Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>:
  foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i0{}, expression, foldExpr.ll_sel.foldExpr{{==}})

def foldStatements(+statements: List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>) -> List<&2, Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>>:
  foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i2{}, Recursion_Syntax.Expr.ll_from2(statements), foldExpr.ll_sel.foldStatements{{==}})

def foldStatement(+statement: Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>) -> Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i1{}>:
  foldExpr.ll_go(Recursion_Syntax.Expr.ll_index.i1{}, statement, foldExpr.ll_sel.foldStatement{{==}})

law folding_sample:
  {foldExpr(Recursion_Syntax.Expr.block{Recursion_Syntax.Expr.ll_from2(Con{Recursion_Syntax.Stmt.assign{"x", Recursion_Syntax.Expr.plus{Recursion_Syntax.Expr.literal{1n, {==}}, Recursion_Syntax.Expr.literal{2n, {==}}, {==}}, {==}}, Nil{}}), Recursion_Syntax.Expr.plus{Recursion_Syntax.Expr.literal{2n, {==}}, Recursion_Syntax.Expr.plus{Recursion_Syntax.Expr.literal{3n, {==}}, Recursion_Syntax.Expr.literal{4n, {==}}, {==}}, {==}}, {==}}) == Recursion_Syntax.Expr.block{Recursion_Syntax.Expr.ll_from2(Con{Recursion_Syntax.Stmt.assign{"x", Recursion_Syntax.Expr.literal{3n, {==}}, {==}}, Nil{}}), Recursion_Syntax.Expr.literal{9n, {==}}, {==}} : Recursion_Syntax.Expr<Recursion_Syntax.Expr.ll_index.i0{}>}

def folding_sample():
  {==}

type walk.ll_sel is Data:
  walk.ll_sel.walk{path: List<&2, Nat>}
  walk.ll_sel.depth{number: Nat}

def walk.ll_out(ll_s: walk.ll_sel) -> Type:
  match ll_s:
    case walk.ll_sel.walk{_}:
      Nat
    case walk.ll_sel.depth{_}:
      Maybe<&2, Nat>

def ll_match55(+ll_v56: Maybe<&2, Nat>, +rest: List<&2, Nat>, ll_k53: @+x: List<&2, Nat> -> Nat, ll_k54: @+x: List<&2, Nat> -> Nat) -> Nat:
  match ll_v56:
    case None{}:
      ll_k53(rest)
    case Some{halvings}:
      L.Lean.Nat.add(halvings, ll_k54(rest))

def ll_match59(+ll_v60: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ll_v60:
    case None{}:
      None{}
    case Some{halvings}:
      Some{L.Lean.Nat.add(halvings, 1n)}

def walk.ll_go(+ll_x: Nat, +ll_s: walk.ll_sel) -> walk.ll_out(ll_s):
  match ll_x:
    case 0n:
      match ll_s:
        case walk.ll_sel.walk{path}:
          0n
        case walk.ll_sel.depth{number}:
          None{}
    case 1n+ll_f52:
      match ll_s:
        case walk.ll_sel.walk{path}:
          match path:
            case Nil{}:
              0n
            case Con{number, rest}:
              ll_match55({walk.ll_go(ll_f52, walk.ll_sel.depth{number}) : Maybe<&2, Nat>}, rest, (+ll_a57 => {walk.ll_go(ll_f52, walk.ll_sel.walk{ll_a57}) : Nat}), (+ll_a58 => {walk.ll_go(ll_f52, walk.ll_sel.walk{ll_a58}) : Nat}))
        case walk.ll_sel.depth{number}:
          match number:
            case 0n:
              Some{{walk.ll_go(ll_f52, walk.ll_sel.walk{Nil{}}) : Nat}}
            case 1n+smaller:
              match smaller:
                case 0n:
                  Some{0n}
                case 1n+lower:
                  ll_match59({walk.ll_go(ll_f52, walk.ll_sel.depth{lower}) : Maybe<&2, Nat>})

def walk(+fuel: Nat, +path: List<&2, Nat>) -> Nat:
  walk.ll_go(fuel, walk.ll_sel.walk{path})

def depth(+fuel: Nat, +number: Nat) -> Maybe<&2, Nat>:
  walk.ll_go(fuel, walk.ll_sel.depth{number})

law walk_sample:
  {walk(10n, Con{4n, Con{7n, Con{1n, Nil{}}}}) == 5n : Nat}

def walk_sample():
  {==}

law walk_exhausted:
  {walk(3n, Con{9n, Nil{}}) == 0n : Nat}

def walk_exhausted():
  {==}

law depth_nine:
  {depth(6n, 9n) == Some{4n} : Maybe<&2, Nat>}

def depth_nine():
  {==}

def ll_match61(+ll_v62: Nat, +head: Nat) -> Nat:
  match ll_v62:
    case 0n:
      head
    case 1n+previous:
      previous

def secondOfTwo(+values: List<&2, Nat>) -> Nat:
  match values:
    case Nil{}:
      0n
    case Con{head, rest}:
      match rest:
        case Nil{}:
          0n
        case Con{later, more}:
          match more:
            case Nil{}:
              ll_match61(later, head)
            case Con{ignored, others}:
              0n

law second_of_two:
  {secondOfTwo(Con{5n, Con{3n, Nil{}}}) == 2n : Nat}

def second_of_two():
  {==}

law second_of_two_zero:
  {secondOfTwo(Con{5n, Con{0n, Nil{}}}) == 5n : Nat}

def second_of_two_zero():
  {==}

def ll_match64(+ll_v65: Bool, +head: Nat, ll_k63: @+x: Unit -> Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ll_v65:
    case True{}:
      Some{head}
    case False{}:
      ll_k63(Unit{})

def firstEven(+values: List<&2, Nat>) -> Maybe<&2, Nat>:
  match values:
    case Nil{}:
      None{}
    case Con{head, rest}:
      ll_match64(isEven(head), head, (+ll_unit => firstEven(rest)))

law first_even:
  {firstEven(Con{3n, Con{5n, Con{8n, Con{2n, Nil{}}}}}) == Some{8n} : Maybe<&2, Nat>}

def first_even():
  {==}

def applyTwice(~ll_E_step: Data, ~step: @+ll_e: ll_E_step -> @+x: Nat -> Nat, +ll_env_step: ll_E_step, +value: Nat) -> Nat:
  step(ll_env_step, step(ll_env_step, value))

def ll_match66(~ll_E_step: Data, ~step: @+ll_e: ll_E_step -> @+x: Nat -> Nat, +ll_v67: Bool, +ll_env_step: ll_E_step, +value: Nat) -> Nat:
  match ll_v67:
    case True{}:
      0n
    case False{}:
      applyTwice(~ll_E_step, ~step, ll_env_step, value)

def stepUnlessZero(~ll_E_step: Data, ~step: @+ll_e: ll_E_step -> @+x: Nat -> Nat, +ll_env_step: ll_E_step, +value: Nat) -> Nat:
  ll_match66(~ll_E_step, ~step, L.Lean.Nat.beq(value, 0n), ll_env_step, value)

law step_unless_zero:
  L.Lean.Prod({stepUnlessZero(~Unit, ~(+ll_e => +n => L.Lean.Nat.add(n, 2n)), Unit{}, 5n) == 9n : Nat}, {stepUnlessZero(~Unit, ~(+ll_e => +n => L.Lean.Nat.add(n, 2n)), Unit{}, 0n) == 0n : Nat})

def step_unless_zero():
  ({==}, {==})

def ll_match68(+ll_v69: List<&2, Nat>, +scale: Nat) -> Nat:
  match ll_v69:
    case Nil{}:
      scale
    case Con{head, rest}:
      L.Lean.Nat.add(head, scale)

def scaledHead(+values: List<&2, Nat>, +factor: Nat) -> Nat:
  +scale = L.Lean.Nat.add(factor, factor)
  ll_match68(values, scale)

law scaled_head:
  L.Lean.Prod({scaledHead(Con{3n, Nil{}}, 2n) == 7n : Nat}, {scaledHead(Nil{}, 2n) == 4n : Nat})

def scaled_head():
  ({==}, {==})

law or_associative:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {L.Lean.Bool.or(L.Lean.Bool.or(a, b), c) == L.Lean.Bool.or(a, L.Lean.Bool.or(b, c)) : Bool}

def or_associative(a, b, c):
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

law less_next:
  for +left: Nat
  for +right: Nat
  {L.Lean.Nat.blt(L.Lean.Nat.add(left, 1n), L.Lean.Nat.add(right, 1n)) == L.Lean.Nat.blt(left, right) : Bool}

def less_next(left, right):
  {==}

law equal_next:
  for +left: Nat
  for +right: Nat
  {L.Lean.Nat.beq(L.Lean.Nat.add(left, 1n), L.Lean.Nat.add(right, 1n)) == L.Lean.Nat.beq(left, right) : Bool}

def equal_next(left, right):
  {==}

def less_successor.ll_ind1(+item: Nat, +bound: Nat) -> {L.Lean.Nat.blt(item, L.Lean.Nat.add(bound, 1n)) == L.Lean.Bool.or(L.Lean.Nat.blt(item, bound), L.Lean.Nat.beq(item, bound)) : Bool}:
  match item:
    case 0n:
      match bound:
        case 0n:
          {==}
        case 1n+smaller:
          {==}
    case 1n+previous:
      match bound:
        case 0n:
          {==}
        case 1n+smaller:
          %Equal.sym(Bool, L.Lean.Nat.beq(L.Lean.Nat.add(previous, 1n), L.Lean.Nat.add(smaller, 1n)), L.Lean.Nat.beq(previous, smaller), equal_next(previous, smaller)) : {L.Lean.Nat.blt(1n+previous, L.Lean.Nat.add(1n+smaller, 1n)) == L.Lean.Bool.or(L.Lean.Nat.blt(1n+previous, 1n+smaller), _) : Bool}
          %Equal.sym(Bool, L.Lean.Nat.blt(L.Lean.Nat.add(previous, 1n), L.Lean.Nat.add(1n+smaller, 1n)), L.Lean.Nat.blt(previous, 1n+smaller), less_next(previous, 1n+smaller)) : {_ == L.Lean.Bool.or(L.Lean.Nat.blt(1n+previous, 1n+smaller), L.Lean.Nat.beq(previous, smaller)) : Bool}
          %Equal.sym(Bool, L.Lean.Nat.blt(previous, L.Lean.Nat.add(smaller, 1n)), L.Lean.Bool.or(L.Lean.Nat.blt(previous, smaller), L.Lean.Nat.beq(previous, smaller)), less_successor.ll_ind1(previous, smaller)) : {_ == L.Lean.Bool.or(L.Lean.Nat.blt(1n+previous, 1n+smaller), L.Lean.Nat.beq(previous, smaller)) : Bool}
          %Equal.sym(Bool, L.Lean.Nat.blt(L.Lean.Nat.add(previous, 1n), L.Lean.Nat.add(smaller, 1n)), L.Lean.Nat.blt(previous, smaller), less_next(previous, smaller)) : {L.Lean.Bool.or(L.Lean.Nat.blt(previous, smaller), L.Lean.Nat.beq(previous, smaller)) == L.Lean.Bool.or(_, L.Lean.Nat.beq(previous, smaller)) : Bool}
          {==}

law less_successor:
  for +item: Nat
  for +bound: Nat
  {L.Lean.Nat.blt(item, L.Lean.Nat.add(bound, 1n)) == L.Lean.Bool.or(L.Lean.Nat.blt(item, bound), L.Lean.Nat.beq(item, bound)) : Bool}

def less_successor(item, bound):
  less_successor.ll_ind1(item, bound)

type Signal is Data:
  Signal.low{}
  Signal.high{}

def isHigh(+signal: Signal) -> Bool:
  match signal:
    case Signal.low{}:
      False{}
    case Signal.high{}:
      True{}

def joinAll(~Item: Data, +front: List<&2, Item>, +back: List<&2, Item>) -> List<&2, Item>:
  match front:
    case Nil{}:
      back
    case Con{head, rest}:
      Con{head, joinAll(~Item, rest, back)}

def anyHigh(+signals: List<&2, Signal>) -> Bool:
  match signals:
    case Nil{}:
      False{}
    case Con{head, rest}:
      L.Lean.Bool.or(isHigh(head), anyHigh(rest))

def any_high_join.ll_ind1(+front: List<&2, Signal>, +back: List<&2, Signal>) -> {anyHigh(joinAll(~Signal, front, back)) == L.Lean.Bool.or(anyHigh(front), anyHigh(back)) : Bool}:
  match front:
    case Nil{}:
      {==}
    case Con{head, rest}:
      %Equal.sym(Bool, anyHigh(joinAll(~Signal, rest, back)), L.Lean.Bool.or(anyHigh(rest), anyHigh(back)), any_high_join.ll_ind1(rest, back)) : {L.Lean.Bool.or(isHigh(head), _) == L.Lean.Bool.or(L.Lean.Bool.or(isHigh(head), anyHigh(rest)), anyHigh(back)) : Bool}
      %Equal.sym(Bool, L.Lean.Bool.or(L.Lean.Bool.or(isHigh(head), anyHigh(rest)), anyHigh(back)), L.Lean.Bool.or(isHigh(head), L.Lean.Bool.or(anyHigh(rest), anyHigh(back))), or_associative(isHigh(head), anyHigh(rest), anyHigh(back))) : {L.Lean.Bool.or(isHigh(head), L.Lean.Bool.or(anyHigh(rest), anyHigh(back))) == _ : Bool}
      {==}

law any_high_join:
  for +front: List<&2, Signal>
  for +back: List<&2, Signal>
  {anyHigh(joinAll(~Signal, front, back)) == L.Lean.Bool.or(anyHigh(front), anyHigh(back)) : Bool}

def any_high_join(front, back):
  any_high_join.ll_ind1(front, back)
