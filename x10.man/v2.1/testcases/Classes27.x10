 package Classes.Assignments.Are.Not.From.Any.Course.Of.Study;
class Oddvec {
  var v : Rail[Int] = Rail.make[Int](3, (Int)=>0);
  public def apply() = "(" + v(0) + "," + v(1) + "," + v(2) + ")";
  public def apply(i:Int) = v(i);
  public def apply(i:Int, j:Int) = [v(i),v(j)];
  public def set(newval:Int, i:Int) = {v(i) = newval;}
  public def set(newval:Int, i:Int, j:Int) = {
       v(i) = newval; v(j) = newval+1;}
  // ...
  public static def main(argv:Rail[String]):Void {
     val a = new Oddvec();
     x10.io.Console.OUT.println(a() + " ... " + a(0));
     a(1) = 20;
     x10.io.Console.OUT.println(a());
     a(0) = 30;
     x10.io.Console.OUT.println(a());
     a(0,1) = 100;
     x10.io.Console.OUT.println(a());
   }
 }