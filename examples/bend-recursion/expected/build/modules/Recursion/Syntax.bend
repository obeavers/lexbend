import Base

type Rose<-Item: Data> is Data:
  Rose.node{a0: Item, a1: List<&2, Rose<Item>>}

type Expr is Data:
  Expr.literal{a0: Nat}
  Expr.plus{a0: Expr, a1: Expr}
  Expr.block{a0: List<&2, Stmt>, a1: Expr}

type Stmt is Data:
  Stmt.assign{a0: String, a1: Expr}
  Stmt.sequence{a0: Stmt, a1: Stmt}

type Term is Data:
  Term.literal{a0: Nat}
  Term.plus{a0: Term, a1: Term}
