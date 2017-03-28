import stainless.lang._
 
object LambdaCalculus {
  abstract class Term
  case class Var(x: BigInt) extends Term
  case class Abs(x: BigInt, body: Term) extends Term
  case class App(func: Term, arg: Term) extends Term
 
  // free variables of t
  def fv(t: Term): Set[BigInt] = t match {
    case Var(x) => Set(x)
    case Abs(x, body) => fv(body) -- Set(x)
    case App(func, arg) => fv(func) ++ fv(arg)
  }
 
  // [x->u]t
  def subst(x: BigInt, u: Term, t: Term): Term = t match {
    case Var(y) => if (x == y) u else t
    case Abs(y, body) => if (x == y) t else Abs(y, subst(x, u, body))
    case App(f, a) => App(subst(x, u, f), subst(x, u, a))
  }
 
  // big step call-by-value evaluation
  /*
   * I feel this question is not very clearly specified. I wrote the postconditions to ensure 
   * that I get a value or none at the end of the evaluation. I also saw that with the termination 
   * command option there are some expressions that don't let the eval function to terminate.
   * 
   * However, I don't understand what I should be doing for solving this problem. Some of the thoughts
   * I gathered (http://stackoverflow.com/questions/42459531/introducing-termination-as-a-precondition-in-leon-stainless)
   * suggest that I should be using a large enough counter that measures the number of possible reductions. 
   * 
   * There are two problems with that solution. First, I must modify the code of eval which is not in principle allowed,
   * second the counter may cause that some terms aren't evaluated and are judged as non-terminating. On the other hand, 
   * this counter could be good for using the decreases construct from stainless.
   * 
   * In this case, I prefer to limit myself to the formulation of the exercise which says "add contracts" and therefore
   * in principle I shouldn't change the code. 
   */
  def eval(t: Term): Option[Term] =  (t match {
    case App(t1, t2) => eval(t1) match {
      case Some(Abs(x, body)) => eval(t2) match {
        case Some(v2) => eval(subst(x, v2, body))
        case None() => None[Term]()
      }
      case _ => None[Term]() // stuck
    }
    case _ => Some(t) // Abs or Var, already a value
   }
  ) ensuring(
	res => res match {
		case None() => true
		case Some(t) => isValue(t)
	}	
  )
 
  def isValue(t: Term): Boolean = t match {
    case Var(x) => true
    case Abs(x, body) => true
    case App(f, a) => false
  }
}
