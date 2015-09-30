package fos

import org.scalacheck.Gen
import org.scalacheck.Gen._

object TreeGenerator {
  sealed trait PredSuccGen {
    def apply(t: Term): Term
  }
  object PredGen extends PredSuccGen {
    def apply(t: Term): Term = Pred(t)
  }
  object SuccGen extends PredSuccGen {
    def apply(t: Term): Term = Succ(t)
  }

  def genPred(t: Term) = Pred(t)
  def genSucc(t: Term) = Succ(t)

  def genValue: Gen[(Term, Term)] = for {
    res <- oneOf(True, False, Zero)
  } yield (res, res)

  def genPredOrSucc: Gen[PredSuccGen] = for {
    op <- oneOf(PredGen, SuccGen)
  } yield op

  def genCondNumber: Gen[(Term, Term)] = for {
    (cond, condRes) <- oneOf(genBool, genIsZero)
    (thn, thnRes) <- genInt
    (els, elsRes) <- genInt
  } yield {
    if(condRes == True) (If(cond, thn, els), thnRes)
    else (If(cond, thn, els), elsRes)
  }

  def genInt: Gen[(Term, Term)] = for {
    n <- posNum[Int]
    ops <- listOfN(n, genPredOrSucc)
  } yield {
    val (result, term) = ops.foldLeft[(Int, Term)]((0, Zero)) {
    case ((0, acc), PredGen) => (0, PredGen(acc))
    case ((count, acc), PredGen) => (count - 1, PredGen(acc))
    case ((count, acc), SuccGen) => (count + 1, SuccGen(acc))
  }

    (term, Arithmetic.desugarNumLit(result))
  }

  def genBool: Gen[(Term, Term)] = for {
    res <- oneOf(True, False)
  } yield (res, res)

  def genIsZero: Gen[(Term, Term)] = for {
    (value, evaluated) <- genInt
  } yield {
    if (evaluated == Zero) (IsZero(value), True)
    else (IsZero(value), False)
  }

  def genIf: Gen[(Term, Term)] = for {
    (cond, condRes) <- oneOf(genBool, genIsZero)
    (thn, thnRes) <- genTerm
    (els, elsRes) <- genTerm
  } yield {
    if (condRes == True) (If(cond, thn, els), thnRes)
    else (If(cond, thn, els), elsRes)
  }

  def genTerm: Gen[(Term, Term)] = for {
    (term, termRes) <- oneOf(genValue, genInt, genCondNumber, genBool, genIf)
  } yield (term, termRes)
}
