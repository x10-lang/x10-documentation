//START TeX: tryargs2
public class TryArgs2 {
   public static def tryargs(var c: Int) {
      c = 1;   // legal to be sure, but will the caller see the new value?
      Console.OUT.print("In tryargs, c is "+c);
   }
   public static def main(args: Array[String](1)): Void {
      var ta2: Int = 0;
      tryargs(ta2);
      Console.OUT.println(".  In main, ta2 is "+ta2);     
   }
}
//END TeX: tryargs2
