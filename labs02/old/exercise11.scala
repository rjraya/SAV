import stainless.lang._
import stainless.collection._
import stainless.proof._
 
object QuickSort {
 
  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }

  def lowerBoundLemma(l1: List[BigInt],l2: List[BigInt],x:BigInt) : Boolean = {
    require(l1.content == l2.content && forall((y : BigInt) => l1.content.contains(y) ==> y <= x))
    forall((z : BigInt) => l2.content.contains(z) ==> z <= x) 
  }.holds

  def upperBoundLemma(l1: List[BigInt],l2: List[BigInt],x:BigInt) : Boolean = {
    require(l1.content == l2.content && forall((y : BigInt) => l1.content.contains(y) ==> y >= x))
    forall((z : BigInt) => l2.content.contains(z) ==> z >= x) 
  }.holds

  def concatIsSortedLemma(l1 : List[BigInt],l2 : List[BigInt],pivot : BigInt) : Boolean = {
    require(isSorted(l1) && isSorted(l2) && l1.forall(_ <= pivot) && l2.forall(_ >= pivot))
    isSorted(l1 ++ Cons(pivot,l2)) because{
      l1 match{
        case Nil() => isSorted(Cons(pivot,l2))
        case Cons(h,Nil()) => h <= pivot && isSorted(Cons(pivot,l2))
        case Cons(h,t) => isSorted(l1) && concatIsSortedLemma(t,l2,pivot)
      }     
    }
  }.holds
 
  def quickSort(list: List[BigInt]): List[BigInt] = (list match {
    case Nil() => Nil[BigInt]()
    case Cons(x, xs) => par(x, Nil(), Nil(), xs)
  }) ensuring { res => isSorted(res) && list.content == res.content && list.size == res.size }
 
  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(l.forall(_ <= x) && r.forall(_ >= x))
    ls match {
      case Nil() => quickSort(l) ++ Cons(x, quickSort(r))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  }ensuring{res => isSorted(res) 
                   because{
                     concatIsSortedLemma(quickSort(l),quickSort(r),x) &&
                     lowerBoundLemma(l,quickSort(l),x) && 
                     upperBoundLemma(r,quickSort(r),x)
                   }  
  }
}
