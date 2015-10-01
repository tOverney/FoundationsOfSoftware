package fos

object CommonTerms {
  val tru       = "(\\t. \\f. t)"
  val fls       = "(\\t. \\f. f)"
  val test      = "(\\x. \\y. \\z. x y z)"
  val and       = s"(\\b. \\c. b c $fls)"
  val or        = s"(\\b. \\c. b $tru c)"
  val not       = s"(\\b. b $fls $tru)"
  val pair      = "(\\f. \\s. \\b. b f s)"
  val fst       = s"(\\p. p $tru)"
  val snd       = s"(\\p. p $fls)"
  val scc       = s"(\\n. \\s. \\z. s (n s z))"
  val zro       = s"(\\s. \\z. z)"
  val one       = s"(\\s. \\z. s z)"
  val two       = s"(\\s. \\z. s (s z))"
  val thr       = s"(\\s. \\z. s (s (s z)))"
  val iszero    = s"(\\m. m (\\x. $fls) $tru)"
  val plus      = s"(\\m. \\n. \\s. \\z. m s (n s z))"
  val times     = s"(\\m. \\n. m ($plus n) $zro)"
  val zz        = s"($pair $zro $zro)"
  val ss        = s"(\\p. $pair ($snd p) ($scc ($snd p)))"
  val prd       = s"(\\m. $fst (m $ss $zz))"
  val fix       = s"(\\f. (\\x. f (\\y. x x y)) (\\x. f (\\y. x x y)))"
  val g         = s"(\\fct. (\\n. ($iszero n) $one ($times n (fct ($prd n)))))"
  val factorial = s"$fix $g"

  def nbr(x: Int) = {
    def inner(y: Int): String = y match {
      case 0 => "z"
      case 1 => "s z"
      case y => s"s (${inner(y - 1)})"
    }
    s"(\\s. \\z. ${inner(x)})"
  }
}
