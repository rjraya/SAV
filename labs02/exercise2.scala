import stainless.lang._
import stainless.collection._
import stainless.proof._
 
object QuickSort {

  def quickSort(list: List[BigInt]): List[BigInt] = {
    decreases((list.size,BigInt(0)))
    list match {
      case Nil() => Nil[BigInt]()
      case Cons(x, xs) => par(x, Nil(), Nil(), xs)
    }
  } ensuring { res => res.content == list.content && res.size == list.size }
 
  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    decreases((l.size+r.size+ls.size,ls.size+1))
    ls match {
      case Nil() => quickSort(l) ++ Cons(x,quickSort(r))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  }ensuring{res => Set(x)++l.content++r.content++ls.content == res.content &&
                   1+l.size+r.size+ls.size == res.size
  }
}