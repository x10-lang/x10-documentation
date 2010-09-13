 package functions2.oh.no;
 import x10.util.*;
 class Finder {
 static

def find[T](f: (T) => Boolean, xs: List[T]!, absent:T): T = {
  for (x: T in xs)
    if (f(x)) return x;
  absent
  }
 }