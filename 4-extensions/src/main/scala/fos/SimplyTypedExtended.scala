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
  def Term: Parser[Term] = (
    rep1(SimpleTerm) ^^ {
      case t::Nil => t
      case elems => elems reduceLeft App
    }
  )
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
    | ("\\" ~> ident) ~ (":" ~> Type) ~ ("." ~> Term) ^^ { 
      case name ~ tpe ~ t => Abs(name, tpe, t)}
    | ("let" ~> ident <~ ":") ~ Type ~ ("=" ~> Term <~ "in") ~ Term ^^ {
      case name ~ tpe ~ t1 ~ t2 => App(Abs(name, tpe, t2), t1)
    }
    | "(" ~> Term <~ ")"
    | ("{" ~> Term <~ ",") ~ (Term <~ "}") ^^ {
      case fst ~ snd => TermPair(fst, snd)
    }
    | "fst" ~> Term ^^ First
    | "snd" ~> Term ^^ Second
  )

  def numToSucc(nv: Int): Term = nv match {
    case 0 => Zero()
    case n => Succ(numToSucc(n - 1))
  }

  /** Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] = (
    genRepSep(genRepSep(BaseType, "*", TypePair), "->", TypeFun)
  )

  def genRepSep(simplerParser: Parser[Type], sep: String,
    outType: (Type, Type) => Type): Parser[Type] = {
    rep1sep(simplerParser, sep) ^^ {
      case x::Nil => x
      case elems => elems reduceRight outType
    }
  }

  // /** SimpleType ::= BaseType [ ("*" SimpleType) | ("+" SimpleType) ]
  //  */
  // def SimpleType: Parser[Type] =
  //   ???

  /** BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] = (
    "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "(" ~> Type <~ ")"
  )


  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    // Computations
    case If(True(), t1, _) => t1
    case If(False(), _, t2) => t2
    case IsZero(Zero()) => True()
    case IsZero(Succ(t1)) if isNumVal(t1) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(t1)) if isNumVal(t1) => t1
    case App(Abs(x, _, t1), v2) if isVal(v2) => subst(t1, x, v2)

    // Congruence
    case If(Reduceable(t1p), t2, t3) => If(t1p, t2, t3)
    case IsZero(Reduceable(t1p)) => IsZero(t1p)
    case Succ(Reduceable(tp)) => Succ(tp)
    case Pred(Reduceable(tp)) => Pred(tp)
    case App(Reduceable(t1p), t2) => App(t1p, t2)
    case App(v1, Reduceable(t2p)) if isVal(v1) => App(v1, t2p)

    // Pair rules
    case First(p @ TermPair(v1, _)) if isVal(p) => v1
    case Second(p @ TermPair(_, v2)) if isVal(p) => v2
    case First(Reduceable(tp)) => First(tp)
    case Second(Reduceable(tp)) => Second(tp)
    case TermPair(Reduceable(t1p), t2) => TermPair(t1p, t2)
    case TermPair(v1, Reduceable(t2p)) if isVal(v1) => TermPair(v1, t2p)
    case _ => throw new NoRuleApplies(t)
  }

  object Reduceable {
    def unapply(t: Term): Option[Term] = {
      try Some(reduce(t))
      catch { case _: Exception => None }
    }

  }

  def isVal(t: Term): Boolean = t match {
    case True() | False() | Abs(_, _, _) => true
    case TermPair(v1, v2) => isVal(v1) && isVal(v2)
    case x => isNumVal(x)
  }

  def isNumVal(t: Term): Boolean = t match {
    case Zero() => true
    case Succ(t1) => isNumVal(t1)
    case _ => false
  }

  def subst(t: Term, x: String, s: Term): Term = t match {
    case Succ(t1) => Succ(subst(t1, x, s))
    case Pred(t1) => Pred(subst(t1, x, s))
    case IsZero(t1) => IsZero(subst(t1, x, s))
    case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
    case First(t1) => First(subst(t1, x, s))
    case Second(t1) => Second(subst(t1, x, s))
    case If(cond, t1, t2) =>
      If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case Var(`x`) => s
    case abs @ Abs(y, tpe, t1) if y != x =>
      if (FV(s)(y)) subst(alpha(abs), x, s)
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
    case Abs(v, _, t1)   => FV(t1) - v
    case App(t1, t2) => FV(t1) ++ FV(t2)
    case TermPair(t1, t2) => FV(t1) ++ FV(t2)
    case First(t1) => FV(t1)
    case Second(t1) => FV(t1)
    case _ => Set.empty
  }

  def alpha(t: Abs): Abs = {
    val Abs(x, tpe, t1) = t
    val y = System.identityHashCode().toString
    Abs(y, tpe, subst(t1, x, Var(y)))
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[Pair[String, Type]]

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = {
    t match {
      case True() | False() => TypeBool
      case Zero() => TypeNat
      case Succ(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeNat
        case otherType => 
          throw new TypeError(t, s"TypeNat expected found $otherType")
      }
      case Pred(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeNat
        case otherType => 
          throw new TypeError(t, s"TypeNat expected found $otherType")
      }
      case IsZero(t1) => typeof(ctx, t1) match {
        case TypeNat => TypeBool
        case otherType =>
          throw new TypeError(t, s"TypeNat expected found $otherType")
      }
      case If(cond, t1, t2) => typeof(ctx, cond) match {
        case TypeBool => 
          val tp1 = typeof(ctx, t1)
          val tp2 = typeof(ctx, t2)
          if (tp1 == tp2) tp1 else throw new TypeError(t, "Type mismatch")
        case ot => throw new TypeError(t, s"TypeBool expected found $ot")
      }
      case Var(x) => ctx.find(_._1 == x).getOrElse(throw new TypeError(t, s"$x is an undefined variable"))._2
      case Abs(x, tpe1, t2) => TypeFun(tpe1, typeof(List((x, tpe1)) ++ ctx, t2))
      case App(t1, t2) => 
        val tpe1 = typeof(ctx, t1)
        val tpe2 = typeof(ctx, t2)
        tpe1 match {
          case TypeFun(`tpe2`, tpe3) => tpe3
          case _ => throw new TypeError(t, "Type parameter mismatch")
        }
      case TermPair(t1, t2) => 
        val tpe1 = typeof(ctx, t1)
        val tpe2 = typeof(ctx, t2)
        TypePair(tpe1, tpe2)
      case First(t1) => typeof(ctx, t1) match {
        case TypePair(tpe1, _) => tpe1
        case ot => throw new TypeError(t, s"TypePair expected found $ot")
      }
      case Second(t1) => typeof(ctx, t1) match {
        case TypePair(_, tpe2) => tpe2
        case ot => throw new TypeError(t, s"TypePair expected found $ot")
      }
    }
  }

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
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
