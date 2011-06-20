//START TeX: arraycopy
public class ArrayCopy {
   public static def main(args: Array[String](1)) {
      val a = [1,2,3];
      Console.OUT.println("initial a is "+a);
      at(here.next()) {
         Console.OUT.println("in at, a is "+a);
         a(1) = 4;                              //\x10lref{arraycopy}{assign}
         Console.OUT.println("after assignment in at, a is "+a); //\x10lref{arraycopy}{after}
      }
      Console.OUT.println("back home, a is "+a); //\x10lref{arraycopy}{backhome}
   }
}
//END TeX: arraycopy