 package functions2.why.is.there.a.two.but.here.is.the.other.one;
 abstract class FunctionsTooManyFlippingFunctions[T, T1, T2]{
 abstract def arg1():T1;
 abstract def arg2():T2;
 def thing1(e:T) {var result:T;
{
  val a1 : T1 = arg1();
  val a2 : T2 = arg2();
  {
     val x1 : T1 = a1;
     val x2 : T2 = a2;
     result = e;
  }
}
}}