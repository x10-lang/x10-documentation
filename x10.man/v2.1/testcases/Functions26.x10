 package functions2.oh.no.my.ears;
 import x10.util.*;
 class Finderator {
 static def find[T](f: (T) => Boolean, xs: x10.util.List[T]!, absent:T): T = {
  for (x: T in xs)
    if (f(x)) return x;
  absent
}
 static def checkery() {
xs: List[Int]! = new ArrayList[Int]();
x: Int = find((x: Int) => x>0, xs, 0);
}}