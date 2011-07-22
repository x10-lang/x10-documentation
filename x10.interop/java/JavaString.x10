import x10.interop.Java;
public class JavaString {
    public static def main(Array[String]) {
        val s:String = "abc";
        val j_s:java.lang.StringBuffer = new java.lang.StringBuffer("abc");
        val ix:Int = s.indexOf("c", 1);
        val j_ix:Java.int = j_s.indexOf("c", 1);
        val chars:Array[Char](1) = s.chars();
        val j_chars:Java.array[Java.char] = new java.io.CharArrayWriter().append(j_s).toCharArray();
        Console.OUT.println("X10 const: '"+s+"'\nJava const: '"+j_s+"'");
        Console.OUT.println("X10 indexOf(): '"+ix+"'\nJava indexOf(): '"+j_ix+"'");
        Console.OUT.println("X10 chars(2): '"+chars(2)+"'\nJava chars(2): '"+j_chars(2)+"'");
    }
}
