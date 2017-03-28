object Bank1 {
  case class Acc(checking : BigInt, savings : BigInt)
 
  /*
   *  I have a.checking >= 0 (1), a.savings >= 0 (2) , a.checking >= x (3)
   *  r is of the form r.checking = a.checking - x, r.savings = a.savings + x
   *  We need to verify r.checking >= 0, r.savings >= 0, a.checking + a.savings = r.checkings + r.savings
   *  
   *  Because (3) we have r.checking >= 0
   *  r.checkings + r.savings = a.checking - x + a.savings + x = a.checking + a.savings
   *  If x is negative then we could have r.savings < 0 so we need that x >= 0
   */
  def putAside(x: BigInt, a: Acc): Acc = {
    require (notRed(a) && a.checking >= x && x >= 0)
    Acc(a.checking - x, a.savings + x)
  } ensuring {
    r => notRed(r) && sameTotal(a, r)
  }
 
 
  def sameTotal(a1: Acc, a2: Acc): Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }
 
  def notRed(a: Acc) : Boolean = {
    a.checking >= 0 && a.savings >= 0
  }
}
