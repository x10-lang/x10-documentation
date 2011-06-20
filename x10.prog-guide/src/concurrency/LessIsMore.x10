import x10.util.Ordered;
public class LessIsMore{
   static def doIt[T](a: T, b: Int) {T <: Ordered[T]}{
      return a < a;
   }
}