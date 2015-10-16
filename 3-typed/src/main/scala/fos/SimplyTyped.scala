package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = (
    rep1(ll1Parsable) ^^ {
      case t::Nil => t
      case elems => elems reduceLeft App
    }

  )

  def ll1Parsable: Parser[Term] = (
    "true" ^^^ True()
    | "false" ^^^ False()
    | "zero" ^^^ Zero()
    | ("if" ~> Term <~ "then") ~ Term ~ ("else" ~> Term) ^^ {
      case cond ~ t1 ~ t2 => If(cond, t1, t2)}
    | numericLit ^^ (x => numToSucc(x.toInt))
    | "succ" ~> Term ^^ Succ
    | "pred" ~> Term ^^ Pred
    | "iszero" ~> Term ^^ IsZero
    | ident ^^ {name => Var(name)}
    | ("\\" ~> ident) ~ (":" ~> parseType) ~ ("." ~> Term) ^^ { 
      case name ~ tpe ~ t => Abs(name, tpe, t)}
    | "(" ~> Term <~ ")"
  )

  def numToSucc(nv: Int): Term = nv match {
    case 0 => Zero()
    case n => Succ(numToSucc(n - 1))
  }

  def parseType: Parser[Type] = (
    rep1sep(parseSimpleType, "->") ^^ {
      case x::Nil => x
      case elems => elems reduceRight TypeFun
    }
  )


  def parseSimpleType: Parser[Type] = (
    "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "(" ~> parseType <~ ")"
  )


  /** Thrown when no reduction rule applies to the given Term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    // Computations
    case If(True(), t1, _) => t1
    case If(False(), _, t2) => t2
    case IsZero(Zero()) => True()
    case IsZero(Succ(t)) if isNumVal(t) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(t)) if isNumVal(t) => t
    case App(Abs(x, _, t1), v2) if isVal(v2) => subst(t1, x, v2)

    // Congruence
    case If(Reduceable(t1p), t2, t3) => If(t1p, t2, t3)
    case IsZero(Reduceable(t1p)) => IsZero(t1p)
    case Succ(Reduceable(tp)) => Succ(tp)
    case Pred(Reduceable(tp)) => Pred(tp)
    case App(Reduceable(t1p), t2) => App(t1p, t2)
    case App(v1, Reduceable(t2p)) if isVal(v1) => App(v1, t2p)
    case t => throw new NoRuleApplies(t)
  }

  object Reduceable {
    def unapply(t: Term): Option[Term] = {
      try Some(reduce(t))
      catch { case _: Exception => None }
    }

  }

  def isVal(t: Term): Boolean = t match {
    case True() | False() | Abs(_, _, _) => true
    case x if isNumVal(x) => true
    case _ => false
  }

  def isNumVal(t: Term): Boolean = t match {
    case Zero() => true
    case Succ(t) => isNumVal(t)
    case _ => false
  }

  def subst(t: Term, x: String, s: Term): Term = t match {
    case Succ(t1) => Succ(subst(t1, x, s))
    case Pred(t1) => Pred(subst(t1, x, s))
    case IsZero(t1) => IsZero(subst(t1, x, s))
    case If(cond, t1, t2) =>
      If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case Var(`x`) => s
    case a @ Abs(y, tpe, t1) if y != x =>
      if (FV(s)(y)) subst(alpha(a), x, s)
      else Abs(y, tpe, subst(t1, x, s))
    case App(t1, t2) =>
      App(subst(t1, x, s), subst(t2, x, s))
    case _ => t
  }

  def FV(t: Term): Set[String] = t match {
    case Var(name)   => Set(name)
    case Succ(t1) => FV(t1)
    case Pred(t1) => FV(t1)
    case IsZero(t1) => FV(t1)
    case If(cond, t1, t2) => FV(cond) ++ FV(t1) ++ FV(t2)
    case Abs(v, _, t)   => FV(t) - v
    case App(t1, t2) => FV(t1) ++ FV(t2)
    case _ => Set.empty
  }

  def alpha(t: Abs): Abs = {
    val Abs(x, tpe, t1) = t
    val y = System.identityHashCode().toString
    Abs(y, tpe, subst(t1, x, Var(y)))
  }

  /** Returns the type of the given Term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given Term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = {
    implicit val ctx0 = ctx
    t match {
      case True() | False() => TypeBool
      case Zero() => TypeNat
      case Succ(TypesTo(TypeNat)) => TypeNat
      case Pred(TypesTo(TypeNat)) => TypeNat
      case IsZero(TypesTo(TypeNat)) => TypeBool
      case If(TypesTo(TypeBool), TypesTo(tp1), TypesTo(tp2)) if tp1 == tp2 =>
        tp1
      case Var(x) => ctx0.find(_._1 == x) match {
        case Some((name, tpe)) => tpe
        case _ => throw new TypeError(t, "Not working")
      }
      case Abs(x, tpe1, t2) => TypeFun(tpe1, typeof(ctx0 :+ (x, tpe1), t2))
      case App(TypesTo(tpe1), TypesTo(tpe2)) => tpe1 match {
        case TypeFun(`tpe2`, tpe3) => tpe3
        case _ => throw new TypeError(t, "Not working")
      } 
      case _ => throw new TypeError(t, "Not working")
    }
  }

  object TypesTo {
    def unapply(t: Term)(implicit ctx0: Context): Option[Type] = 
      try Some(typeof(ctx0, t))
      catch {
        case _: Exception => None
      }
  }


  /** Returns a stream of Terms, each being one step of reduction.
   *
   *  @param t      the initial Term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of Terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
