package fos

import fos.CommonTerms._
import fos.Untyped._
import fos.Utils.TermOps
import org.scalatest.{FlatSpec, Matchers}

abstract class UntypedTest extends FlatSpec with Matchers {

  def evaluationStrategy(t: Term): Term

  def parse(input: String): Term = {
    val tokens = new lexical.Scanner(input)
    phrase(term)(tokens) match {
      case Success(trees, _) => trees
      case NoSuccess(msg, _) => fail(msg)
    }
  }

  def eval(term: String, expected: String) = {
    it should s"reduce $term to $expected" in {
      val pTerm = parse(term)
      val pExpected = parse(expected)
      val reduced = path(pTerm, evaluationStrategy).last
      assert(reduced isAEquivTo pExpected, s"$reduced did not equal $pExpected")
    }
  }

  // Tests common to all reduction strategies
  eval("x", "x")
  eval("(\\n. l m n)", "(\\n. l m n)")
  eval(s"$test $tru $one $two", one)
  eval(s"$test $fls $one $two", two)
  eval(s"$and $tru $tru", tru)
  eval(s"$and $tru $fls", fls)
  eval(s"$and $fls $tru", fls)
  eval(s"$and $fls $fls", fls)
  eval(s"$or $tru $tru", tru)
  eval(s"$or $tru $fls", tru)
  eval(s"$or $fls $tru", tru)
  eval(s"$or $fls $fls", fls)
  eval(s"${CommonTerms.not} $tru", fls)
  eval(s"${CommonTerms.not} $fls", tru)
  eval(s"$fst ($pair $one $two)", one)
  eval(s"$snd ($pair $one $two)", two)
  eval(s"$iszero $zro", tru)
  eval(s"$iszero $two", fls)

  // Reduces to itself => infinite loop
  // eval("(\\x. x x) (\\x. x x)", "(\\x. x x) (\\x. x x)")

  // Recursion only works under "call by name" evaluation strategy
  // eval(s"$factorial $zro", s"$one")
  // eval(s"$factorial $one", s"$one")
}

class NormalOrder extends UntypedTest {
  def evaluationStrategy(t: Term): Term = reduceNormalOrder(t)

  // Tests specific to normal order
  eval("(\\x. y) z", "y")
  eval("\\y. ((\\x. x) y)", "\\y. y")
  eval("(\\x. y) z x", "y x")
  eval("(\\x. y) z (\\x. y) z", "y (\\x. y) z")
  eval("(\\a. (\\b. c) d) e", "c")
  eval("\\y. ((\\x.x) y)", "\\y. y")
  eval("(\\x. (\\y. x y)) y", "\\x. y x")
  eval(s"(\\x. x) ((\\x. x) (\\z. (\\x. x) z))", "\\z. z")

  // For some reason, tests with "succ" fail with call by value
  // Under "call by value" reduces to behavioral equivalen terms 
  eval(s"$scc $zro", one)
  eval(s"$scc $one", two)
  eval(s"$scc $two", thr)
  eval(s"$scc ($scc $zro)", two)
  eval(s"$scc ($scc ($scc $zro))", thr)
  eval(s"$scc ($scc ($scc ($scc $zro)))", nbr(4))
  eval(s"$times $one $two", s"$two")
  eval(s"$times ${nbr(3)} ${nbr(4)}", nbr(12))
  eval(s"$prd $thr", two)
  eval(s"$prd $zro", zro)
}

class CallByValue extends UntypedTest {
  def evaluationStrategy(t: Term): Term = reduceCallByValue(t)

  // Tests specific to call by value
  eval("(\\x. y) z", "(\\x. y) z")
  eval("\\y. ((\\x. x) y)", "\\y. ((\\x. x) y)")
}
