 package Activities.Atomic.Redund.One;
 import x10.util.*;
 class Redund[T] {
   val list = new ArrayList[T]();
   var size : Int = 0;
def add(x:T) { // Incorrect
  this.list.add(x);
  this.size = this.size + 1;
}
}