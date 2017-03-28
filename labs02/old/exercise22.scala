import stainless.lang._
import stainless.collection._
 
object QuickSort {
 
  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }
 
  def quickSort(list: List[BigInt]): List[BigInt] = {
    decreases((list.size,BigInt(0)))
    list match {
      case Nil() => Nil[BigInt]()
      case Cons(x, xs) => 
        par(x, Nil(), Nil(), xs)
    }
  } ensuring { res => isSorted(res) }
 
  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    decreases((l.size+r.size+ls.size,ls.size+1))
    ls match {
      case Nil() => 
        quickSort(l) ++ Cons(x, quickSort(r))
      case Cons(x2, xs2) => 
        if (x2 <= x){ 
          par(x, Cons(x2, l), r, xs2) 
        }else{
          par(x, l, Cons(x2, r), xs2)
        }  
    }
  }
}