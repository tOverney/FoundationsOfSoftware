package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] =
    rep1(SimpleTerm) ^^ {
      case List(t) => t
      case ts      => ts reduceLeft App
    }

  /** SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident ":" Type "." Term
   *               | "(" Term ")"
   *               | "let" ident ":" Type "=" Term "in" Term
   *               | "{" Term "," Term "}"
   *               | "fst" Term
   *               | "snd" Term
   *               | "inl" Term "as" Type
   *               | "inr" Term "as" Type
   *               | "case" Term "of" "inl" ident "=>" Term "|" "inr" ident "=>" Term
   *               | "fix" Term
   *               | "letrec" ident ":" Type "=" Term "in" Term</pre>
   */
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
    | inl
    | inr
    | cse
    | fix
    | letrec
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
  def let         = "let" ~> ident ~ (":" ~> Type <~ "=") ~ Term ~ ("in" ~> Term) ^^ { case v ~ tp ~ t1 ~ t2 => App(Abs(v, tp, t2), t1) }
  def letrec      = "letrec" ~> ident ~ (":" ~> Type <~ "=") ~ Term ~ ("in" ~> Term) ^^ { case v ~ tp ~ t1 ~ t2 => App(Abs(v, tp, t2), Fix(Abs(v, tp, t1))) }
  def pair        = "{" ~> Term ~ ("," ~> Term <~ "}") ^^ { case t1 ~ t2 => TermPair(t1, t2) }
  def first       = "fst" ~> Term ^^ First
  def second      = "snd" ~> Term ^^ Second
  def inl         = "inl" ~> Term ~ ("as" ~> Type) ^^ { case t ~ tpe => Inl(t, tpe) }
  def inr         = "inr" ~> Term ~ ("as" ~> Type) ^^ { case t ~ tpe => Inr(t, tpe) }
  def fix         = "fix" ~> Term ^^ Fix
  def cse         = "case" ~> (Term <~ "of" ~ "inl") ~ ident ~ ("=>" ~> Term) ~ ("|" ~ "inr" ~> ident) ~ ("=>" ~> Term) ^^ {
    case t ~ x1 ~ t1 ~ x2  ~ t2 => Case(t, x1, t1, x2, t2)
  }

  /** Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] =
    SimpleType ~ opt("->" ~> Type) ^^ {
      case tp1 ~ Some(tp2) => TypeFun(tp1, tp2)
      case tp ~ None       => tp
    }

  /** SimpleType ::= BaseType [ ("*" SimpleType) | ("+" SimpleType) ]
   */
  def SimpleType: Parser[Type] =
    BaseType ~ opt("*" ~ SimpleType | "+" ~ SimpleType) ^^ {
      case tp1 ~ Some("*" ~ tp2) => TypePair(tp1, tp2)
      case tp1 ~ Some("+" ~ tp2) => TypeSum(tp1, tp2)
      case tp ~ None             => tp
    }

  /** BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] = (
      "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "(" ~> Type <~ ")"
  )

  def desugarNumLit(x: Int): Term =
    if (x == 0) Zero()
    else Succ(desugarNumLit(x - 1))

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
    case Succ(t)                  => Succ(subst(t, x, s))
    case Pred(t)                  => Pred(subst(t, x, s))
    case IsZero(t)                => IsZero(subst(t, x, s))
    case If(cond, t1, t2)         => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case Var(`x`)                 => s
    case Abs(y, tp, t1) if y != x => Abs(y, tp, subst(t1, x, s))
    case App(t1, t2)              => App(subst(t1, x, s), subst(t2, x, s))
    case TermPair(t1, t2)         => TermPair(subst(t1, x, s), subst(t2, x, s))
    case First(t)                 => First(subst(t, x, s))
    case Second(t)                => Second(subst(t, x, s))
    case Inl(t, tp)               => Inl(subst(t, x, s), tp)
    case Inr(t, tp)               => Inr(subst(t, x, s), tp)

    case Case(t, x1, t1, x2, t2) =>
      val st1 = if (x1 != x) subst(t1, x, s) else t1
      val st2 = if (x2 != x) subst(t2, x, s) else t2
      Case(subst(t, x, s), x1, st1, x2, st2)

    case Fix(t) => Fix(subst(t, x, s))
    case _      => t
  }

  def isV(t: Term): Boolean = t match {
    case True() | False() | _: Abs => true
    case TermPair(t1, t2)          => isV(t1) && isV(t2)
    case Inr(v, _)                 => isV(v)
    case Inl(v, _)                 => isV(v)
    case _                         => isNV(t)
  }

  def isNV(t: Term): Boolean = t match {
    case Zero()   => true
    case Succ(nv) => isNV(nv)
    case _        => false
  }

  object Reduced {
    def unapply(t: Term): Option[Term] =
      try Some(reduce(t))
      catch { case _: NoRuleApplies => None }
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
    case Case(Inl(v, _), x1, t1, _, _) if isV(v)        => subst(t1, x1, v)
    case Case(Inr(v, _), _, _, x2, t2) if isV(v)        => subst(t2, x2, v)
    case Fix(Abs(x, tp, t2))                            => subst(t2, x, t)

    // Congruence Rules
    case If(Reduced(c), t1, t2)               => If(c, t1, t2)
    case IsZero(Reduced(nv))                  => IsZero(nv)
    case Succ(Reduced(nv))                    => Succ(nv)
    case Pred(Reduced(nv))                    => Pred(nv)
    case App(Reduced(t1), t2)                 => App(t1, t2)
    case App(v, Reduced(t))        if isV(v)  => App(v, t)
    case First(Reduced(t))                    => First(t)
    case Second(Reduced(t))                   => Second(t)
    case TermPair(Reduced(t1), t2)            => TermPair(t1, t2)
    case TermPair(t1, Reduced(t2)) if isV(t1) => TermPair(t1, t2)
    case Inl(Reduced(t), tp)                  => Inl(t, tp)
    case Inr(Reduced(t), tp)                  => Inr(t, tp)
    case Case(Reduced(t), x1, t1, x2, t2)     => Case(t, x1, t1, x2, t2)
    case Fix(Reduced(t))                      => Fix(t)

    case _ => throw new NoRuleApplies(t)
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

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
      typeof(ctx, n) match {
        case TypeNat =>
          TypeNat
        case tp =>
          throw new TypeError(t, s"type mismatch: expected $TypeNat, found $tp")
      }

    case Succ(n) =>
      typeof(ctx, n) match {
        case TypeNat =>
          TypeNat
        case tp =>
          throw new TypeError(t, s"type mismatch: expected $TypeNat, found $tp")
      }

    case IsZero(n) =>
      typeof(ctx, n) match {
        case TypeNat =>
          TypeBool
        case tp =>
          throw new TypeError(t, s"type mismatch: expected $TypeNat, found $tp")
      }

    case If(cond, t1, t2) =>
      typeof(ctx, cond) match {
        case TypeBool =>
          val tp1 = typeof(ctx, t1)
          val tp2 = typeof(ctx, t2)
          if (tp1 == tp2) tp1
          else throw new TypeError(t, s"type mismatch: expected $tp1, found $tp2")

        case tp =>
          throw new TypeError(t, s"type mismatch: expected $TypeBool, found $tp")
      }

    case Var(name) =>
      ctx find (_._1 == name) map (_._2) getOrElse {
        throw new TypeError(t, s"undefined variable $name")
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
          throw new TypeError(t, s"type mismatch: expected $tp2 -> T, found $tp1")
      }

    case TermPair(t1, t2) =>
      val tp1 = typeof(ctx, t1)
      val tp2 = typeof(ctx, t2)
      TypePair(tp1, tp2)

    case First(p) =>
      typeof(ctx, p) match {
        case TypePair(tp, _) =>
          tp
        case tp =>
          throw new TypeError(t, s"pair type expected but $tp found")
      }

    case Second(p) =>
      typeof(ctx, p) match {
        case TypePair(_, tp) =>
          tp
        case tp =>
          throw new TypeError(t, s"pair type expected but $tp found")
      }

    case Inl(t0, tp) =>
      val tp1 = typeof(ctx, t0)
      tp match {
        case TypeSum(`tp1`, tp2) =>
          tp
        case _ =>
          throw new TypeError(t, s"($tp1, T) expected but $tp found")
      }

    case Inr(t0, tp) =>
      val tp2 = typeof(ctx, t0)
      tp match {
        case TypeSum(tp1, `tp2`) =>
          tp
        case _ =>
          throw new TypeError(t, s"(T, $tp2) expected but $tp found")
      }

    case Case(t0, x1, t1, x2, t2) =>
      typeof(ctx, t0) match {
        case TypeSum(tp1, tp2) =>
          val tp3 = typeof((x1, tp1) :: ctx, t1)
          val tp4 = typeof((x2, tp2) :: ctx, t2)
          if (tp3 == tp4) tp3
          else throw new TypeError(t, s"type mismatch expected: $tp3 found $tp4")

        case tp =>
          throw new TypeError(t, s"sum type expected but $tp found")
      }

    case Fix(t0) =>
      typeof(ctx, t0) match {
        case TypeFun(tp1, tp2) if tp1 == tp2 =>
          tp1
        case tp =>
          throw new TypeError(t, s"identity function type expected but $tp found")
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
          println("parsed: " + trees)
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
