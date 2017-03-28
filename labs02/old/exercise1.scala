import stainless.lang._
import stainless.collection._
import stainless.proof._

object QuickSort {

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }

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

  /*def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  })*/
   
  def sortPreservesLowerBounds(l : List[BigInt],pivot : BigInt) = {
    require(l.forall(_ <= pivot))   
    quickSort(l)
  }ensuring{res => res.forall(_ <= pivot) because{
    res match{
      case Nil() => true
      case Cons(h,t) => l.content.contains(h) && 
    }  
   }
  } 
   
  def quickSortPreservesUpperBounds(l : List[BigInt],pivot : BigInt) = {
    require(l.forall(_ >= pivot))   
    quickSort(l)
  }ensuring{res => res.forall(_ >= pivot) because{
    res.forall(x => l.exists(y => y == x && y >= pivot))
   }
  } 
  
  def quickSort(list: List[BigInt]): List[BigInt] = (list match {
        case Nil() => Nil[BigInt]()
        case Cons(x, xs) => par(x, Nil(), Nil(), xs)
  }) ensuring { res => isSorted(res) && list.content == res.content && list.size == res.size}

  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(l.forall(_ <= x) && r.forall(_ >= x))
    ls match {
      case Nil() => quickSort(l) ++ Cons(x,quickSort(r))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  } ensuring {res => isSorted(res) && 
                     Set(x)++l.content++r.content++ls.content == res.content && 
                     1+l.size+r.size+ls.size == res.size because{
                     concatIsSortedLemma(quickSort(l),quickSort(r),x)
                    }
  }
}
