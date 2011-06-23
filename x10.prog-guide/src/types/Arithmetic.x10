//START TeX: arith
public interface Arithmetic[T] { // \xlref{arith-decl}
   def add(t: T): T; // \xlref{arith-startdefs}
   def subtract(t: T): T;
   def multiply(t: T): T;
   def divide(t: T): T;
   public static VERSION = "1.1";   // \xlref{arith-enddefs}
}
//END TeX: arith
