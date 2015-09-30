package fos

import org.scalatest.prop.GeneratorDrivenPropertyChecks
import org.scalatest.{FlatSpec, Matchers}

class ArithmeticTest extends FlatSpec with Matchers with GeneratorDrivenPropertyChecks {

  import Arithmetic._

  def parse(input: String): Term = {
    val tokens = new lexical.Scanner(input)
    phrase(term)(tokens) match {
      case Arithmetic.Success(trees, _) => trees
      case _                            => fail()
    }
  }

  "eval" should "perform reduction when possible" in {
    val parsed = parse("if iszero pred pred 2 then if iszero 0 then true else false else false")
    eval(parsed) shouldBe True

    forAll(TreeGenerator.genValue) {
      case (term, expected) =>
        eval(term) shouldBe expected
    }

//    forAll(TreeGenerator.genTerm) {
//      case (term, expected) =>
//        eval(term) shouldBe expected
//    }
  }

  it should "throw TermIsStuck exception if reduction is not possible" in {
    val parsed = parse("pred succ succ succ false")
    val thrown = the [TermIsStuck] thrownBy eval(parsed)
    thrown.t shouldBe Succ(False)
  }

  "reduce" should "perform reduction when possible" in {
    val parsed = parse("if iszero pred pred 2 then if iszero 0 then true else false else false")
    val expectedPath = List(
      If(IsZero(Pred(Pred(Succ(Succ(Zero))))),If(IsZero(Zero),True,False),False),
      If(IsZero(Pred(Succ(Zero))),If(IsZero(Zero),True,False),False),
      If(IsZero(Zero),If(IsZero(Zero),True,False),False),
      If(True,If(IsZero(Zero),True,False),False),
      If(IsZero(Zero),True,False),
      If(True,True,False),
      True
    )
    path(parsed) shouldBe expectedPath

    forAll(TreeGenerator.genValue) {
      case (term, expected) =>
        path(term).last shouldBe expected
    }

//    forAll(TreeGenerator.genTerm) {
//      case (term, expected) =>
//        path(term).last shouldBe expected
//    }
  }

  it should "throw NoReductionPossible exception if reduction is not possible" in {
    val parsed = parse("pred succ succ succ false")
    val thrown = the [NoReductionPossible] thrownBy reduce(parsed)
    thrown.t shouldBe Pred(Succ(Succ(Succ(False))))
  }



}
