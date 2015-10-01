package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import scala.util.Try

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | '0'
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */

  def term: Parser[Term] = (
      "true" ^^^ True
    | "false" ^^^ False
    | "0" ^^^ Zero
    | "succ" ~> term ^^ Succ
    | "pred" ~> term ^^ Pred
    | numericLit ^^ (x => numToSucc(x.toInt))
    | "iszero" ~> term ^^ IsZero
    | parseIf
  )

  def numToSucc(nv: Int): Term = nv match {
    case 0 => Zero
    case n => Succ(numToSucc(n - 1))
  }

  def parseIf: Parser[Term] = (
      "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^ {
        case "if" ~ cond ~ "then" ~ t1 ~ "else" ~ t2 =>
          If(cond, t1, t2)
      }
    )

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match {
    case If(True, t1, t2) => t1
    case If(False, t1, t2) => t2
    case IsZero(Zero) => True
    case IsZero(Succ(t)) if isNumVal(t) => False
    case Pred(Zero) => Zero
    case Pred(Succ(t)) if isNumVal(t) => t
    case If(cond, t1, t2) => If(reduce(cond), t1, t2)
    case IsZero(term) if Try(reduce(term)).isSuccess => IsZero(reduce(term))
    case Pred(term) if Try(reduce(term)).isSuccess => Pred(reduce(term))
    case Succ(term) if Try(reduce(term)).isSuccess => Succ(reduce(term))
    case _ => throw NoReductionPossible(t)
  }

  def isNumVal(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t) => isNumVal(t)
    case _ => false
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = t match {
    case True | False | Zero => t
    case Succ(term) if isNumVal(eval(term)) => Succ(eval(term))
    case If(cond, t1, t2) if eval(cond) == True => eval(t1)
    case If(cond, t1, t2) if eval(cond) == False => eval(t2)
    case Pred(t1) => eval(t1) match {
      case Zero => Zero
      case Succ(t2) if isNumVal(t2) => t2
      case _ => throw TermIsStuck(t)
    }
    case IsZero(t1) if eval(t1) == Zero => True
    case IsZero(t1) if isNumVal(eval(t1)) => False
    case _ => throw TermIsStuck(t)
  }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
