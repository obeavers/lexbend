import Base

type Rose<-Item: Data> is Data:
  Rose.node{a0: Item, a1: List<&2, Rose<Item>>}

type Expr.ll_index is Data:
  Expr.ll_index.i0{}
  Expr.ll_index.i1{}
  Expr.ll_index.i2{}

type Expr<-ll_i: Expr.ll_index> is Data:
  Expr.literal{a0: Nat, ll_e: {ll_i == Expr.ll_index.i0{} : Expr.ll_index}}
  Expr.plus{a0: Expr<Expr.ll_index.i0{}>, a1: Expr<Expr.ll_index.i0{}>, ll_e: {ll_i == Expr.ll_index.i0{} : Expr.ll_index}}
  Expr.block{a0: Expr<Expr.ll_index.i2{}>, a1: Expr<Expr.ll_index.i0{}>, ll_e: {ll_i == Expr.ll_index.i0{} : Expr.ll_index}}
  Stmt.assign{a0: String, a1: Expr<Expr.ll_index.i0{}>, ll_e: {ll_i == Expr.ll_index.i1{} : Expr.ll_index}}
  Stmt.sequence{a0: Expr<Expr.ll_index.i1{}>, a1: Expr<Expr.ll_index.i1{}>, ll_e: {ll_i == Expr.ll_index.i1{} : Expr.ll_index}}
  Expr.ll_nil2{ll_e: {ll_i == Expr.ll_index.i2{} : Expr.ll_index}}
  Expr.ll_cons2{a0: Expr<Expr.ll_index.i1{}>, a1: Expr<Expr.ll_index.i2{}>, ll_e: {ll_i == Expr.ll_index.i2{} : Expr.ll_index}}

def Expr.ll_not0(+ll_k: Expr.ll_index) -> Type:
  match ll_k:
    case Expr.ll_index.i0{}:
      Empty
    case Expr.ll_index.i1{}:
      Unit
    case Expr.ll_index.i2{}:
      Unit

def Expr.ll_not1(+ll_k: Expr.ll_index) -> Type:
  match ll_k:
    case Expr.ll_index.i0{}:
      Unit
    case Expr.ll_index.i1{}:
      Empty
    case Expr.ll_index.i2{}:
      Unit

def Expr.ll_not2(+ll_k: Expr.ll_index) -> Type:
  match ll_k:
    case Expr.ll_index.i0{}:
      Unit
    case Expr.ll_index.i1{}:
      Unit
    case Expr.ll_index.i2{}:
      Empty

def Expr.ll_clash0_1(ll_h: {Expr.ll_index.i0{} == Expr.ll_index.i1{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not1(_)
  Unit{}

def Expr.ll_clash0_2(ll_h: {Expr.ll_index.i0{} == Expr.ll_index.i2{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not2(_)
  Unit{}

def Expr.ll_clash1_0(ll_h: {Expr.ll_index.i1{} == Expr.ll_index.i0{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not0(_)
  Unit{}

def Expr.ll_clash1_2(ll_h: {Expr.ll_index.i1{} == Expr.ll_index.i2{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not2(_)
  Unit{}

def Expr.ll_clash2_0(ll_h: {Expr.ll_index.i2{} == Expr.ll_index.i0{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not0(_)
  Unit{}

def Expr.ll_clash2_1(ll_h: {Expr.ll_index.i2{} == Expr.ll_index.i1{} : Expr.ll_index}) -> Empty:
  %ll_h : Expr.ll_not1(_)
  Unit{}

def Expr.ll_from2(+ll_xs: List<&2, Expr<Expr.ll_index.i1{}>>) -> Expr<Expr.ll_index.i2{}>:
  match ll_xs:
    case Nil{}:
      Expr.ll_nil2{{==}}
    case Con{ll_h, ll_t}:
      Expr.ll_cons2{ll_h, Expr.ll_from2(ll_t), {==}}

def Expr.ll_to2(+ll_x: Expr<Expr.ll_index.i2{}>) -> List<&2, Expr<Expr.ll_index.i1{}>>:
  match ll_x:
    case Expr.literal{_, ll_e}:
      Empty.absurd(List<&2, Expr<Expr.ll_index.i1{}>>, Expr.ll_clash2_0(ll_e))
    case Expr.plus{_, _, ll_e}:
      Empty.absurd(List<&2, Expr<Expr.ll_index.i1{}>>, Expr.ll_clash2_0(ll_e))
    case Expr.block{_, _, ll_e}:
      Empty.absurd(List<&2, Expr<Expr.ll_index.i1{}>>, Expr.ll_clash2_0(ll_e))
    case Stmt.assign{_, _, ll_e}:
      Empty.absurd(List<&2, Expr<Expr.ll_index.i1{}>>, Expr.ll_clash2_1(ll_e))
    case Stmt.sequence{_, _, ll_e}:
      Empty.absurd(List<&2, Expr<Expr.ll_index.i1{}>>, Expr.ll_clash2_1(ll_e))
    case Expr.ll_nil2{_}:
      Nil{}
    case Expr.ll_cons2{ll_h, ll_t, _}:
      Con{ll_h, Expr.ll_to2(ll_t)}

type Term is Data:
  Term.literal{a0: Nat}
  Term.plus{a0: Term, a1: Term}
