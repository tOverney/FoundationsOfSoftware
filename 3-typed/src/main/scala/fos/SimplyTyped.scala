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
  def Term: Parser[Term] =
    rep1(SimpleTerm) ^^ {
      case List(t) => t
      case ts      => ts reduceLeft App
    }

  def SimpleTerm: Parser[Term] = (
      truev
    | falsev
    | ift
    | integer
    | predecessor
    | successor
    | iszero
    | variable
    | abstraction
    | let
    | pair
    | first
    | second
    | "(" ~> Term <~ ")"
  )

  def truev       = "true" ^^^ True()
  def falsev      = "false" ^^^ False()
  def ift         = "if" ~> Term ~ ("then" ~> Term <~ "else") ~ Term ^^ { case cond ~ t1 ~ t2 => If(cond, t1, t2)}
  def integer     = numericLit ^^ (x => desugarNumLit(x.toInt))
  def predecessor = "pred" ~> Term ^^ Pred
  def successor   = "succ" ~> Term ^^ Succ
  def iszero      = "iszero" ~> Term ^^ IsZero
  def variable    = ident ^^ Var
  def abstraction = "\\" ~> ident ~ (":" ~> Type <~ ".") ~ Term ^^ { case v ~  tp ~ t => Abs(v, tp, t) }
  def let         =  "let" ~> ident ~ (":" ~> Type <~ "=") ~ Term ~ ("in" ~> Term) ^^ { case v ~ tp ~ t2 ~ t1 => App(Abs(v, tp, t2), t1) }
  def pair        = "{" ~> Term ~ ("," ~> Term <~ "}") ^^ { case t1 ~ t2 => TermPair(t1, t2) }
  def first       = "fst" ~> Term ^^ First
  def second      = "snd" ~> Term ^^ Second

  def Type: Parser[Type] =
    rep1sep(Pairtype, "->") ^^ {
      case List(t) => t
      case ts      => ts reduceRight TypeFun
    }

  def Pairtype: Parser[Type] =
    rep1sep(SimpleType, "*") ^^ {
      case List(t) => t
      case ts      => ts reduceRight TypePair
    }

  def SimpleType: Parser[Type] = (
      "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "(" ~> Type <~ ")"
  )

  def desugarNumLit(x: Int): Term =
    if (x == 0) Zero()
    else Succ(desugarNumLit(x - 1))


  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  object ReduceTo {
    def unapply(t: Term): Option[Term] =
      try Some(reduce(t))
      catch { case _: NoRuleApplies => None }
  }

  /** <p>
    *    Alpha conversion: term <code>t</code> should be a lambda abstraction
    *    <code>\x. t</code>.
    *  </p>
    *  <p>
    *    All free occurences of <code>x</code> inside term <code>t/code>
    *    will be renamed to a unique name.
    *  </p>
    *
    *  @param t the given lambda abstraction.
    *  @return  the transformed term with bound variables renamed.
    */
  def alpha(t: Abs): Abs = {
    val Abs(x, tp, t1) = t
    val y = freshName(x)
    Abs(y, tp, subst(t1, x, Var(y)))
  }

  private var count = 0

  def freshName(prefix: String): String = {
    val fresh = s"$prefix$count"
    count += 1
    fresh
  }

  /** Straight forward substitution method
    *  (see definition 5.3.5 in TAPL book).
    *  [x -> s]t
    *
    *  @param t the term in which we perform substitution
    *  @param x the variable name
    *  @param s the term we replace x with
    *  @return  ...
    */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case Succ(t)          => Succ(subst(t, x, s))
    case Pred(t)          => Pred(subst(t, x, s))
    case IsZero(t)        => IsZero(subst(t, x, s))
    case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))

    case a @ Abs(y, tp, t1) if y != x =>
      if (FV(s) contains y) subst(alpha(a), x, s)
      else Abs(y, tp, subst(t1, x, s))

    case App(t1, t2) =>
      App(subst(t1, x, s), subst(t2, x, s))

    case Var(`x`)  => s
    case First(t)  => First(subst(t, x, s))
    case Second(t) => Second(subst(t, x, s))
    case _         => t
  }

  def isV(t: Term): Boolean = t match {
    case True() | False() | _: Abs => true
    case TermPair(t1, t2)          => isV(t1) && isV(t2)
    case _                         => isNV(t)
  }

  def isNV(t: Term): Boolean = t match {
    case Zero()   => true
    case Succ(nv) => isNV(nv)
    case _        => false
  }

  def FV(t: Term): Set[String] = t match {
    case Succ(t)          => FV(t)
    case Pred(t)          => FV(t)
    case IsZero(t)        => FV(t)
    case If(cond, t1, t2) => FV(cond) ++ FV(t1) ++ FV(t2)
    case Var(name)        => Set(name)
    case Abs(v, _, t)     => FV(t) - v
    case App(t1, t2)      => FV(t1) ++ FV(t2)
    case _                => Set.empty
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    // Computation Rules
    case If(True(), t1, _)                              => t1
    case If(False(), _, t2)                             => t2
    case IsZero(Zero())                                 => True()
    case IsZero(Succ(nv))         if isNV(nv)           => False()
    case Pred(Zero())                                   => Zero()
    case Pred(Succ(nv))           if isNV(nv)           => nv
    case App(Abs(x, _, t), v)     if isV(v)             => subst(t, x, v)
    case First(TermPair(t1, t2))  if isV(t1) && isV(t2) => t1
    case Second(TermPair(t1, t2)) if isV(t1) && isV(t2) => t2

    // Congruence Rules
    case If(ReduceTo(c), t1, t2)        => If(c, t1, t2)
    case IsZero(ReduceTo(nv))           => IsZero(nv)
    case Succ(ReduceTo(nv))             => Succ(nv)
    case Pred(ReduceTo(nv))             => Pred(nv)
    case App(ReduceTo(t1), t2)          => App(t1, t2)
    case App(v, ReduceTo(t)) if isV(v)  => App(v, t)
    case First(ReduceTo(t))             => First(t)
    case Second(ReduceTo(t))            => First(t)
    case TermPair(ReduceTo(t1), t2)     => TermPair(t1, t2)
    case TermPair(t1, ReduceTo(t2))     => TermPair(t1, t2)

    case _                              => throw new NoRuleApplies(t)
  }

  def checkType(ctx: Context, t: Term, expected: Type): Unit = {
    val tp = typeof(ctx, t)
    if (tp != expected)
      throw new TypeError(t, s"type mismatch: expected $expected, found $tp")
  }

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() | False() =>
      TypeBool

    case Zero() =>
      TypeNat

    case Pred(n) =>
      checkType(ctx, n, TypeNat)
      TypeNat

    case Succ(n) =>
      checkType(ctx, n, TypeNat)
      TypeNat

    case IsZero(n) =>
      checkType(ctx, n, TypeNat)
      TypeBool

    case If(cond, t1, t2) =>
      checkType(ctx, cond, TypeBool)
      val tp1 = typeof(ctx, t1)
      checkType(ctx, t2, tp1)
      tp1

    case Var(name) =>
      ctx find (_._1 == name) map (_._2) match {
        case Some(tp) => tp
        case _        => throw new TypeError(t, s"undefined variable $name")
      }

    case Abs(x, tp1, t) =>
      val tp2 = typeof((x, tp1) :: ctx, t)
      TypeFun(tp1, tp2)

    case App(t1, t2) =>
      val tp1 = typeof(ctx, t1)
      val tp2 = typeof(ctx, t2)
      tp1 match {
        case TypeFun(`tp2`, tp) =>
          tp
        case _ =>
          throw new TypeError(t, s"parameter type mismatch: expected $tp2, found $tp1")
      }

    case TermPair(t1, t2) =>
      val tp1 = typeof(ctx, t1)
      val tp2 = typeof(ctx, t2)
      TypePair(tp1, tp2)

    case First(t) =>
      typeof(ctx, t) match {
        case TypePair(tp, _) =>
          tp
        case tp =>
          throw new TypeError(t, s"pair type expected but $tp found")
      }

    case Second(t) =>
      typeof(ctx, t) match {
        case TypePair(_, tp) =>
          tp
        case tp =>
          throw new TypeError(t, s"pair type expected but $tp found")
      }
  }


  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      val t1 = reduce(t)
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
          case TypeError(t: Term, msg: String) => println(s"$msg\n$t")
        }
      case e =>
        println(e)
    }
  }
}
