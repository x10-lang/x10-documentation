 package Activities.Atomic.Redund.Two;
 import x10.util.*;
 class Redund[T] {
   val list = new ArrayList[T]();
   var size : Int = 0;
def add(x:T) {
  this.list.add(x);
  atomic { this.size = this.size + 1; }
}
}