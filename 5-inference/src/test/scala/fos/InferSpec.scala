package fos

import fos.Parser._
import org.scalatest.{FlatSpec, Matchers}

class InferSpec extends FlatSpec with Matchers with CustomMatchers {

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

  "Valid Terms" should "type check" in {

    "\\x. succ x" should typeTo ("Nat -> Nat")
    "\\x. if x then 1 else 2" should typeTo ("Bool -> Nat")
    "\\x. if x then x else x" should typeTo ("Bool -> Bool")
    "\\b. if b then false else true" should typeTo ("Bool -> Bool")
    "\\x. \\y. if iszero (x y) then 1 else y" should typeTo ("(Nat -> Nat) -> (Nat -> Nat)")
    "let x = 1 in succ x" should typeTo ("Nat")
    "let cond = true in if cond then 1 else 2" should typeTo ("Nat")
    "let identity = \\x. x in if (identity true) then (identity 1) else (identity 2)" should typeTo ("Nat")
    "let identity = \\x. x in let toNat = \\x. if (identity x) then (identity 1) else (identity 0) in toNat true" should typeTo ("Nat")
    "let identity = \\x. x in let toBool = \\x. if (iszero x) then (identity false) else (identity true) in toBool 3" should typeTo ("Bool")
    "let double = \\f.\\x.f(f(x)) in if (double (\\x:Bool. if x then false else true) false) then double (\\x:Nat.succ x) 0 else 0" should typeTo ("Nat")
  }

  "Not valid terms" should "not typecheck" in {

    "\\b. if b then 1 else true" shouldNot typeCheck2
    "(\\f.\\x. let g = f in g(0)) (\\x.if x then false else true) true" shouldNot typeCheck2
  }
}
