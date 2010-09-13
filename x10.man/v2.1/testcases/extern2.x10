 package Extern.or.burn;
import x10.compiler.Native;
class Land {
  @Native("c++", "printf(\"Hi from C++!\")")
  static def example():Void = {
    x10.io.Console.OUT.println("Hi from X10!");
  };
}
