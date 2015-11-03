package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")
  
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
    | ifTerm
    | numericLit ^^ (x => desugarNumLit(x.toInt))
    | "succ" ~> term ^^ Succ
    | "pred" ~> term ^^ Pred
    | "iszero" ~> term ^^ IsZero
    | failure("unexpected term"))

  def ifTerm: Parser[If] =
    "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^ {
      case "if" ~ cond ~ "then" ~ thn ~ "else" ~ els =>
        If(cond, thn, els)
    }

  def desugarNumLit(x: Int): Term =
    if (x == 0) Zero
    else Succ(desugarNumLit(x - 1))

  def isV(t: Term) =
    t == True || t == False || isNV(t)

  def isNV(t: Term): Boolean = t match {
    case Zero     => true
    case Succ(nv) => isNV(nv)
    case _        => false
  }

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

  object ReduceTo {
    def unapply(t: Term): Option[Term] =
      try Some(reduce(t))
      catch { case _: NoReductionPossible => None }
  }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match {
    case If(True, t1, _)              => t1
    case If(False, _, t2)             => t2
    case IsZero(Zero)                 => True
    case IsZero(Succ(nv)) if isNV(nv) => False
    case Pred(Zero)                   => Zero
    case Pred(Succ(nv)) if isNV(nv)   => nv
    case If(ReduceTo(c), t1, t2)      => If(c, t1, t2)
    case IsZero(ReduceTo(nv))         => IsZero(nv)
    case Pred(ReduceTo(nv))           => Pred(nv)
    case Succ(ReduceTo(nv))           => Succ(nv)
    case _                            => throw NoReductionPossible(t)
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  object EvalTo {
    def unapply(t: Term): Option[Term] =
      Some(eval(t))
  }

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = t match {
    case _ if isV(t)                               => t
    case If(EvalTo(True), EvalTo(v), _) if isV(v)  => v
    case If(EvalTo(False), _, EvalTo(v)) if isV(v) => v
    case Succ(EvalTo(nv)) if isNV(nv)              => Succ(nv)
    case Pred(EvalTo(Zero))                        => Zero
    case Pred(EvalTo(Succ(nv))) if isNV(nv)        => nv
    case IsZero(EvalTo(Zero))                      => True
    case IsZero(EvalTo(Succ(nv))) if isNV(nv)      => False
    case _                                         => throw TermIsStuck(t)
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
