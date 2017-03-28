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

  def concatIsSortedLemma(l1 : List[BigInt],l2 : List[BigInt],pivot : BigInt) : List[BigInt] = {
    require(isSorted(l1) && isSorted(l2) && 
            forall((z : BigInt) => l1.content.contains(z) ==> z <= pivot)  && 
            forall((z : BigInt) => l2.content.contains(z) ==> z >= pivot) 
           )
    l1 ++ Cons(pivot,l2)
  }ensuring{res => isSorted(res) because{
      l1 match{
        case Nil() => isSorted(Cons(pivot,l2))
        case Cons(h,Nil()) => h <= pivot && isSorted(Cons(pivot,l2))
        case Cons(h,t) => isSorted(l1) && isSorted(concatIsSortedLemma(t,l2,pivot))
      }     
    } &&
    Set(pivot) ++ l1.content ++ l2.content == res.content &&
    1 + l1.size + l2.size == res.size
  }

  def quickSort(list: List[BigInt]): List[BigInt] = (list match {
    case Nil() => Nil[BigInt]()
    case Cons(x, xs) => par(x, Nil(), Nil(), xs)
  }) ensuring { res => isSorted(res) && res.content == list.content && res.size == list.size }
 
  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(forall((z : BigInt) => l.content.contains(z) ==> z <= x)  && 
            forall((z : BigInt) => r.content.contains(z) ==> z >= x) )
    ls match {
      case Nil() => concatIsSortedLemma(quickSort(l),quickSort(r),x) 
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  }ensuring{res => isSorted(res) because{
                    lowerBoundLemma(l,quickSort(l),x) &&
                    upperBoundLemma(r,quickSort(r),x)
                   } &&
                   Set(x)++l.content++r.content++ls.content == res.content &&
                   1+l.size+r.size+ls.size == res.size
  }
}
