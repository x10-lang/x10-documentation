//START TeX: tryargs
public class TryArgs {
   public static def tryargs(val a: Int, b: Int, var c: Int) {
      a = b = 1;  // illegal: a and b are both vals!
      c = 1;       // legal: c is declare to be a var.
   }
}
//END TeX: tryargs
