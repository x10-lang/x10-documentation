import x10.interop.Java;
public class JavaString {
    public static def main(Array[String]) {
        val s:String = "aaa";
        val ix:Int = s.indexOf("a", 1);
        val chars:Array[Char] = s.chars();
        //val j_chars:Java.array[Java.char] = j_s.toCharArray();	// java.lang.String API unavailable
    }
}
