package fos

import fos.Parser._
import org.scalatest.{FunSuite, Matchers}

class InferTest extends FunSuite with Matchers with CustomMatchers {

  override def parseTerm(in: String): Term = {
    val tokens = new lexical.Scanner(in)
    phrase(Term)(tokens) match {
      case Success(term, _) => term
      case _                => fail()
    }
  }

  override def parseType(in: String) = {
    val tokens = new lexical.Scanner(in)
    phrase(Type)(tokens) match {
      case Success(tpe, _) => tpe
      case _               => fail()
    }
  }

  override def typeOf(term: Term) = {
    val (tpe, c) = Infer.collect(Nil, term)
    val sub = Infer.unify(c)
    sub(tpe)
  }

  test("Should type checks valid terms") {
    "\\x. succ x" should typeTo ("(Nat -> Nat)")
    "\\x. if x then 1 else 2" should typeTo ("(Bool -> Nat)")
    "\\x. if x then x else x" should typeTo ("(Bool -> Bool)")
    "(\\b. if b then false else true)" should typeTo ("(Bool -> Bool)")
    "\\x. \\y. if iszero (x y) then 1 else y" should typeTo ("((Nat -> Nat) -> (Nat -> Nat))")
    //"let double = \\f.\\x.f(f(x)) in if (double (\\x:Bool. if x then false else true) false) then double (\\x:Nat.succ x) 0 else 0" should typeTo ("Nat")
  }

  test("Should not type check not valid terms") {
    "\\b. if b then 1 else true" shouldNot typeCheck2
    //"(\\f.\\x. let g = f in g(0)) (\\x.if x then false else true) true" shouldNot typeCheck
  }
}
