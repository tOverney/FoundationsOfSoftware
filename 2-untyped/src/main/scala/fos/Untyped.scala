package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] =
      rep1(simpleTerm) ^^ {
        case List(t) => t
        case ts      => ts reduceLeft App
      }

  def simpleTerm: Parser[Term] = (
      "(" ~> term <~ ")"
    | ident ^^ Var
    | "\\" ~ ident ~ "." ~ term ^^ { case "\\" ~ name ~ "." ~ t => Abs(name, t) }
  )


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
    val Abs(x, t1) = t
    val y = freshName(x)
    Abs(y, subst(t1, x, Var(y)))
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
  def subst(t: Term, x: String, s: Term): Term =
    t match {
      case Var(`x`) => s

      case a @ Abs(y, t1) if y != x =>
        if (FV(s) contains y) subst(alpha(a), x, s)
        else Abs(y, subst(t1, x, s))

      case App(t1, t2) =>
        App(subst(t1, x, s), subst(t2, x, s))

      case _ => t
    }

  def FV(t: Term): Set[String] =
    t match {
      case Var(name)   => Set(name)
      case Abs(v, t)   => FV(t) - v
      case App(t1, t2) => FV(t1) ++ FV(t2)
    }

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  object ReduceNTo {
    def unapply(t: Term): Option[Term] =
      try Some(reduceNormalOrder(t))
      catch { case _: NoReductionPossible => None }
  }

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term =
    t match {
      case App(Abs(x, t1), t2)    => subst(t1, x, t2)
      case App(ReduceNTo(t1), t2) => App(t1, t2)
      case App(t1, ReduceNTo(t2)) => App(t1, t2)
      case Abs(x, ReduceNTo(t1))  => Abs(x, t1)
      case _                      => throw new NoReductionPossible(t)
    }

  def isV(t: Term): Boolean =
    t.isInstanceOf[Abs]

  object ReduceCTo {
    def unapply(t: Term): Option[Term] =
      try Some(reduceCallByValue(t))
      catch { case _: NoReductionPossible => None }
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term =
    t match {
      case App(ReduceCTo(t1), t2)         => App(t1, t2)
      case App(v, ReduceCTo(t)) if isV(v) => App(v, t)
      case App(Abs(x, t), v) if isV(v)    => subst(t, x, v)
      case _                              => throw new NoReductionPossible(t)
    }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      val t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
