import x10.interop.Java;
public class JavaString {
    public static def main(Array[String]) {
        val s:String = "aaa";
        val j_s:String = new java.util.StringBuffer("aaa").toString();
        val ix:Int = s.indexOf("a", 1);
        val j_ix:Java.int = j_s.indexOf("a", 1);
        val chars:Array[Char] = s.chars();
        val j_chars:Java.array[Java.char] = j_s.toCharArray(); // invalid (not exposed)
        Console.OUT.println("X10 const: '"+s+"'\nJava const: '"+j_s+"'");
        Console.OUT.println("X10 indexOf(): '"+ix+"'\nJava indexOf(): '"+j_ix+"'");
        Console.OUT.println("X10 chars(2): '"+chars(2)+"'\nJava chars(2): '"+j_chars(2)+"'");
    }
}
