package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
  *  untyped lambda calculus found in Chapter 5 of
  *  the TAPL book.
  */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
    | '\' x '.' t
    | t t
    | '(' t ')'
    */
  def term: Parser[Term] = rep1(simpleTerm) ^^ {
    case List(t) => t
    case ts => ts reduceLeft App
  }

  def simpleTerm : Parser[Term] = ( varTerm
    | absTerm
    | parensTerm
  )

  def varTerm : Parser[Term] = ident ^^ Var
  def absTerm : Parser[Term] = "\\" ~> ident ~ "." ~ term ^^ {
    case name ~ "."~ term => Abs(name, term)
  }
  def parensTerm : Parser[Term] = "(" ~> term <~ ")"

  def fvOf(t : Term) : List[String] = {
    def inner(boundVar : List[String], t1 : Term, acc : List[String]) : List[String] = t1 match {
      case Abs(x, y) => inner(x :: boundVar, y, acc)
      case App(x, y) => inner(boundVar, x, acc) ::: inner(boundVar, y, acc)
      case Var(y) => if (! boundVar.contains(y)) y :: acc else Nil
    }

    inner(List(), t, List())
  }


  def isValue(t : Term) : Boolean = t.isInstanceOf[Abs]

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
  def alpha(t: Term): Term = {
    t match {
      case Abs(x, t) => {
        val name = newName(x)
        Abs(x, subst(t, x, Var(name)))
      }
      case _ => t
    }
  }

  private var num = 0

  def newName(orig : String) : String = {
    val name = s"$orig$num"
    num = num + 1
    name
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
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
    case Abs(y, t1) if fvOf(s) contains y => subst(t1, x, s)
    case Abs(y, t1) => subst(t1, x, alpha(s))
    case Var(y) if y == x => s
    case Var(_) | Abs(_, _) => t
  }


  object ReduceNormalOrderTo {
    def unapply(t: Term) : Option[Term] = {
      try Some(reduceNormalOrder(t))
      catch { case _ : NoReductionPossible => None }
    }
  }


  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
    *
    *  @param t the initial term
    *  @return  the reduced term
    */
  def reduceNormalOrder(t: Term): Term = t match {
    case App(ReduceNormalOrderTo(t1), t2) => App(t1, t2)
    case App(t1, ReduceNormalOrderTo(t2)) => App(t1, t2)
    case Abs(x, ReduceNormalOrderTo(t1)) => Abs(x, t1)
    case App(Abs(x, t1), t) => subst(t1, x, t)
    case _ => throw new NoReductionPossible(t)
  }


  object ReduceByValueTo {
    def unapply(t : Term) : Option[Term] = {
      try Some(reduceCallByValue(t))
      catch { case _ : NoReductionPossible => None}
    }
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = t match {
    case App(ReduceByValueTo(t1), t2) => App(t1, t2)
    case App(t1, ReduceByValueTo(t2)) if isValue(t2) => App(t1, t2)
    case App(Abs(x, t1), a) if isValue(a) => subst(t1, x, a)
    case _ => throw new NoReductionPossible(t)
  }

  /** Returns a stream of terms, each being one step of reduction.
    *
    *  @param t      the initial term
    *  @param reduce the method that reduces a term by one step.
    *  @return       the stream of terms representing the big reduction.
    */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
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
