package Extern.or.Die;
import x10.compiler.Native;
class Ability {
  static val a : Int = 1;
  @Native("java", "a")
  static native def fromStatic():Int;
}
