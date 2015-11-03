package fos

import fos.Untyped._

object Utils {

  implicit class TermOps(val self: Term) extends AnyVal {

    /* is this alpha equivalent to that */
    def isAEquivTo(that: Term): Boolean = (self, that) match {
      case (Var(x), Var(y)) if x == y => true

      case (Abs(v1, t1), Abs(v2, t2)) =>
        if (v1 == v2) t1 isAEquivTo t2
        else {
          val fresh = freshName("v")
          val freshVar = Var(fresh)
          Abs(fresh, subst(t1, v1, freshVar)) isAEquivTo Abs(fresh, subst(t2, v2, freshVar))
        }

      case (App(t1, t2), App(t3, t4)) => (t1 isAEquivTo t3) && (t2 isAEquivTo t4)
      case _                          => false
    }
  }
}
