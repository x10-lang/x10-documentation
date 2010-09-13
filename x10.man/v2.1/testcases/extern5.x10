 package Extern.or_current_turn;
import x10.compiler.Native;
class Species {
  @Native("c++", "printf(\"Sum=%d\", ((#1)+(#2)) )")
  @Native("java", "System.out.println(\"Hi!\")")
  static native def printNatively(x:Int, y:Int):Void;
}
