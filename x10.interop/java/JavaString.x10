import x10.interop.Java;
public class JavaString {
    public static def main(Array[String]) {
        val s:String = "aaa";
        val j_s:java.lang.String = Java.convert("aaa");
        val ix:Int = s.indexOf("a", 1);
        val j_ix:Java.int = j_s.indexOf(Java.convert("a"), Java.convert(1));
        val chars:Array[Char] = s.chars();
        val j_chars:Java.array[Java.char] = j_s.toCharArray();
        Console.OUT.println("X10 const: '"+s+"'\nJava const: '"+Java.convert(j_s)+"'");
        Console.OUT.println("X10 indexOf(): '"+ix+"'\nJava indexOf(): '"+Java.convert(j_ix)+"'");
        Console.OUT.println("X10 chars(2): '"+chars(2)+"'\nJava chars(2): '"+Java.convert(j_chars)(2)+"'");
    }
}
