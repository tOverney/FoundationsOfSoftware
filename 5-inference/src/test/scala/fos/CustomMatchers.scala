package fos

import org.scalatest.matchers.{MatchResult, Matcher}

import scala.util.Try

trait CustomMatchers {

  def parseTerm(in: String): Term
  def parseType(in: String): TypeTree
  def typeOf(term: Term): Type

  class TermTypesTo(right: String) extends Matcher[String] {
    override def apply(left: String): MatchResult = {
      val term = parseTerm(left)
      val tpe = parseType(right).tpe
      val result = typeOf(term)

      MatchResult(
        tpe == result,
        s"$left types to $result, expected $tpe",
        s"$left types to $tpe"
      )
    }
  }

  class TermTypeChecks extends Matcher[String] {
    override def apply(left: String): MatchResult = {
      val term = parseTerm(left)
      val result = Try(typeOf(term))

      MatchResult(
        result.isSuccess,
        s"$left does not type check",
        s"$left type checks"
      )
    }
  }

  def typeTo(tpe: String) = new TermTypesTo(tpe)
  def typeCheck2 = new TermTypeChecks
}
