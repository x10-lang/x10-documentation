//START TeX: classvsstruct
public class ClassVsStruct {
  static class  Class(a:Int)  {}
  static struct Struct(a:Int) {}
  public static def main(argv:Array[String](1)) {
    val c <: Class  = new Class(1);
    val d <: Class  = new Class(1);
    val s <: Struct = Struct(1);
    val t <: Struct = Struct(1);
    assert c != d;
    assert s == t;
  }
}
//END TeX: classvsstruct
