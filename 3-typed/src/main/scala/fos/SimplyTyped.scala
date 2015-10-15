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
  def Term: Parser[Term] = rep1(simpleTerm) ^^ {
    case List(t) => t
    case ts => ts reduceLeft App
  }

  def deSugar(x : Int) : Term = x match {
    case 0 => Zero()
    case v => Succ(deSugar(x - 1))
  }

  def simpleTerm : Parser[Term] = {
    values |
    ifTerm |
    isZero |
    let |
    "(" ~> Term <~ ")"
  }

  def tp : Parser[Type] = {
    rep1sep(simpleType, "->") ^^ {
      case List(t) => t
      case ts => ts reduceRight TypeFun
    } |
    rep1sep(simpleType, "*") ^^ {
      case List(t) => t
      case ts => ts reduceRight TypePair
    }
  }

  def simpleType : Parser[Type] = {
    "Nat" ^^^ TypeNat |
    "Bool" ^^^ TypeBool
  }

  def booleanTerm : Parser[Term] = "true" ^^^ True() | "false" ^^^ False()
  def numericValue : Parser[Term] = {
    numericLit ^^ (x => deSugar(x.toInt)) |
    "pred" ~> Term ^^ (x => Pred(x)) |
    "succ" ~> Term ^^ (x => Succ(x))
  }
  def variable : Parser[Term] = ident ^^ Var

  def values : Parser[Term] = (
    booleanTerm
      | numericValue
      | variable
      | abstraction
      | pair
      | extract)

  def abstraction : Parser[Term] = "\\" ~> variable ~ ":" ~ tp ~ "." ~ Term ^^ {
    case variable ~ ":" ~ typ ~ "." ~ body => Abs(variable.toString, typ, body)
  }

  def ifTerm : Parser[Term] = "if" ~> Term ~ "then" ~ Term ~ "else" ~ Term ^^ {
    case cond ~ "then" ~ thn ~ "else" ~ els => If(cond, thn, els)
      }

  def isZero : Parser[Term] = "iszero" ~> Term ^^ (x => IsZero(x))

  def let : Parser[Term] = "let" ~> ident ~ ":" ~ tp ~ "=" ~ Term ~ "in" ~ Term ^^ {
    case name ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(name, tp, t2), t1)
  }

  def pair : Parser[Term] = "{" ~> values ~ "," ~ values <~ "}" ^^ {
    case v1 ~ "," ~ v2 => TermPair(v1, v2)
  }

  def extract : Parser[Term] = "fst" ~> values ^^ First | "snd" ~> values ^^ Second


  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  def isNv(v : Term) : Boolean = v match {
    case Succ(v1) => isNv(v1)
    case Zero() => true
    case _ => false
  }

  def fvOf(t : Term) : Set[String] = t match {
    case Var(x) => Set(x)
    case Abs(x, _, t1) => fvOf(t1) - x
    case App(t1, t2) => fvOf(t1) ++ fvOf(t2)
    case If(cnd, thn, els) => fvOf(cnd) ++ fvOf(thn) ++ fvOf(els)
    case IsZero(t) => fvOf(t)
    case Succ(t) => fvOf(t)
    case Pred(t) => fvOf(t)
    case TermPair(fst, snd) => fvOf(fst) ++ fvOf(snd)
    case First(pair) => fvOf(pair)
    case Second(pair) => fvOf(pair)

    case _ => Set.empty
  }

  def isValue(t : Term) : Boolean = t match  {
    case True() | False() | Abs(_, _, _) | Succ(_) | Zero() => true
    case _ => false
  }

  def subst(t : Term, x : String, s : Term) : Term = t match {
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
    case Abs(x, tp, t1) if ! fvOf(s).contains(x) => subst(t1, x, s)
    case Abs(x, tp, t1) => subst(t1, x, alpha(s))
    case If(cnd, thn, els) => If(subst(cnd, x, s), subst(thn, x, s), subst(els, x, s))
      case Var(y) if x == y => s
    case TermPair(fst, snd) => TermPair(subst(fst, x, s), subst(snd, x, s))
    case First(pair) => First(subst(pair, x, s))
    case Second(pair) => Second(subst(pair, x, s))
    case _ => t
  }

  def alpha(t : Term) : Term = t match {
    case Abs(x, tp, t) => {
      val name = freshName(x)
      Abs(x, tp, subst(t, x, Var(name)))
    }
    case _ => t
  }

  private var count = 0

  def freshName(orig : String) : String = {
    val name = s"$orig$count"
    count = count + 1
    name
  }

  object ReduceTo {
    def unapply(t : Term) : Option[Term] = {
      try { Some(reduce(t)) }
      catch { case _ : NoRuleApplies => None }
    }
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case If(True(), t1, _) => t1
    case If(False(), _, t2) => t2
    case IsZero(Zero()) => True()
    case IsZero(Succ(v)) if isNv(v) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(v)) if isNv(v) => v
    case App(Abs(x, typ, t1), v2) => subst(t1, x, v2)
    case First(TermPair(v1, _)) => v1
    case Second(TermPair(_, v2)) => v2

    // Congruence rules
    case If(ReduceTo(cond), t1, t2) => If(cond, t1, t2)
    case Succ(ReduceTo(t1)) => Succ(t1)
    case IsZero(ReduceTo(t1)) => IsZero(t1)
    case Pred(ReduceTo(t1)) => Pred(t1)
    case App(ReduceTo(t1), t2) => App(t1, t2)
    case App(v1, ReduceTo(t2)) => App(v1, t2)
    case First(ReduceTo(t)) => First(t)
    case Second(ReduceTo(t)) => Second(t)
    case TermPair(ReduceTo(t1), t2) => TermPair(t1, t2)
    case TermPair(t1, ReduceTo(t2)) => TermPair(t1, t2)

    case _ => throw new NoRuleApplies(t)
  }

  /** Returns the type of the given term <code>t</code>.
    *
    *  @param ctx the initial context
    *  @param t   the given term
    *  @return    the computed type
    */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() | False() => TypeBool
    case Zero() => TypeNat
    case Succ(v) if typeof(ctx, v) == TypeNat => TypeNat
    case Pred(v) if typeof(ctx, v) == TypeNat => TypeNat
    case IsZero(v) if typeof(ctx, v) == TypeNat => TypeBool
    case If(cnd, thn, els)
      if typeof(ctx, cnd) == TypeBool &&
        typeof(ctx, thn) == typeof(ctx, els) => typeof(ctx, thn)
    case Var(x) => ctx.find(y => y._1 == x) match {
      case Some(tp) => tp._2
      case None => throw new TypeError(t, "Reference to free variable " + x)
    }
    case Abs(x, t, body) => TypeFun(t, typeof((x, t):: ctx, body))
    case App(t1, t2) => typeof(ctx, t1) match {
      case TypeFun(t11, t12) => {
        val argType = typeof(ctx, t2)
        if (argType == t11) t12
        else throw new TypeError(t, "Parameter type mismatch expected " +
          t11 + " but got " + argType)
      }
      case _ => throw new TypeError(t, "Applying " + t1 +
          " which is not an abstraction!")
    }
    case TermPair(fst, snd) => TypePair(typeof(ctx, fst), typeof(ctx, snd))
    case First(pair) => typeof(ctx, pair) match {
      case TypePair(t1, _) => t1
      case _ => throw new TypeError(t, pair + " is not a pair")
    }
    case Second(pair) => typeof(ctx, pair) match {
      case TypePair(_, t2) => t2
      case _ => throw new TypeError(t, pair + " is not a pair")
    }

    case _ => throw new TypeError(t, "Unknown type error")
  }



  /** Returns a stream of terms, each being one step of reduction.
    *
    *  @param t      the initial term
    *  @param reduce the evaluation strategy used for reduction.
    *  @return       the stream of terms representing the big reduction.
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
