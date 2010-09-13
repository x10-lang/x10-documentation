 package Activities.Condato.Example.Not.A.Tree;
 import x10.util.*;
 class Redund[T] {
 val list = new ArrayList[T]();
 var size : Int = 0;
def pop():T {
  var ret : T;
  when(size>0) {
    ret = list.removeAt(0);
    size --;
    }
  return ret;
}
 }