package fos

object Infer {

  case class TypeScheme(params: List[TypeVar], tp: Type) {
    def instantiate: Type = {
      val subst = (params foldLeft Substitution.empty) {
        case (acc, tv @ TypeVar(name)) =>
          acc + (tv -> freshType())
      }
      subst(tp)
    }
  }

  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    case True() | False() =>
      (BoolType, Nil)

    case Zero() =>
      (NatType, Nil)

    case Pred(t1) =>
      val (tp, c) = collect(env, t1)
      (NatType, (tp, NatType) :: c)

    case Succ(t1) =>
      val (tp, c) = collect(env, t1)
      (NatType, (tp, NatType) :: c)

    case IsZero(t1) =>
      val (tp, c) = collect(env, t1)
      (BoolType, (tp, NatType) :: c)

    case If(t1, t2, t3) =>
      val (tp1, c1) = collect(env, t1)
      val (tp2, c2) = collect(env, t2)
      val (tp3, c3) = collect(env, t3)
      (tp2, (tp1, BoolType) :: (tp2, tp3) :: c1 ::: c2 ::: c3)

    case Var(name) =>
      val ts = env find (_._1 == name) map (_._2) getOrElse {
        throw new TypeError(s"free variable $name")
      }
      (ts.instantiate, Nil)

    case Abs(x, tpTree, t1) =>
      val tp1 =
        if (tpTree.isInstanceOf[EmptyTypeTree]) freshType()
        else tpTree.tpe
      val (tp2, c) = collect((x, TypeScheme(Nil, tp1)) :: env, t1)
      (FunType(tp1, tp2), c)

    case App(t1, t2) =>
      val (tp1, c1) = collect(env, t1)
      val (tp2, c2) = collect(env, t2)
      val tp = freshType()
      (tp, (tp1, FunType(tp2, tp)) :: c1 ::: c2)

    case Let(x, EmptyTypeTree(), t1, t2) =>
      val (s1, c1) = collect(env, t1)
      val sub = unify(c1)
      val tp1 = sub(s1)
      val env2 = env map {
        case (name, TypeScheme(ps, tp)) =>
          (name, TypeScheme(ps, sub(tp)))
      }
      val params = tp1.vars --
        (env2 map (_._2.tp.vars) fold Set.empty)(_ ++ _)

      val (tp2, c2) = collect((x, TypeScheme(params.toList, tp1)) :: env2, t2)
      (tp2, c1 ::: c2)

    case Let(x, tpTree, t1, t2) =>
      collect(env, App(Abs(x, tpTree, t2), t1))
  }

  def unify(cs: List[Constraint]): Type => Type =
    unify(cs, Substitution.empty)

  private def unify(cs: List[Constraint], subst: Substitution): Substitution =
    cs match {
      case (tp1, tp2) :: rest if tp1 == tp2 =>
        unify(rest, subst)

      case (tp1: TypeVar, tp2) :: rest =>
        unify(tp1, tp2, rest, subst)

      case (tp1, tp2: TypeVar) :: rest =>
        unify(tp2, tp1, rest, subst)

      case (FunType(from1, to1), FunType(from2, to2)) :: rest =>
        unify((from1, from2) :: (to1, to2) :: rest, subst)

      case (tp1, tp2) :: _ =>
        throw new TypeError(s"Could not unify: $tp1 with $tp2")

      case Nil =>
        subst
    }

  private def unify(tp1: TypeVar, tp2: Type, cs: List[Constraint], subst: Substitution): Substitution =
    if (tp2 contains tp1) throw new TypeError("Could not unify")
    else {
      val nsubst = subst + (tp1 -> tp2)
      val ncs = cs map {
        case (t1, t2) =>
          (nsubst(t1), nsubst(t2))
      }
      unify(ncs, nsubst)
    }

  private var count = 0

  private def freshType(prefix: String = "T") = {
    val tpe = TypeVar(s"$prefix$count")
    count += 1
    tpe
  }

  class Substitution private (subst: Map[Type, Type]) extends (Type => Type) {
    def apply(from: Type): Type = {
      val to = subst getOrElse (from, {
        from match {
          case FunType(t1, t2) => FunType(apply(t1), apply(t2))
          case _               => from
        }
      })

      if (from == to) from
      else apply(to)
    }

    def +(pair: (Type, Type)): Substitution =
      new Substitution(subst + pair)

    override def toString = subst.toString
  }

  object Substitution {
    def apply(from: Type, to: Type): Substitution =
      empty + (from -> to)

    def empty: Substitution = new Substitution(Map.empty)
  }

  implicit class TypeOps(val tpe: Type) extends AnyVal {
    def contains(thatTpe: Type): Boolean = tpe match {
      case `thatTpe`       => true
      case FunType(t1, t2) => (t1 contains thatTpe) || (t2 contains thatTpe)
      case _               => false
    }

    def vars: Set[TypeVar] = tpe match {
      case tpVar: TypeVar  => Set(tpVar)
      case FunType(t1, t2) => t1.vars ++ t2.vars
      case _               => Set.empty
    }
  }
}
