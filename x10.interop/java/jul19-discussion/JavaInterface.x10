import x10.interop.Java;
public class JavaInterface {
    public static class MyString(s:String) implements java.lang.CharSequence { // it's okay to implement java interface
        def charAt(index:Java.int):Java.char {
            return Java.convert(s(index));		// Char type needs conversion to Java.char
        }
        def length():Java.int {
            return s.length();
        }
        def subSequence(start:Java.int, end:Java.int):java.lang.CharSequence {
            return new MyString(s.substring(start, end));
        }
        def toString():String {
            return s;
        }
    }
    public static def main(Array[String]) {
        val j_s = "abc";
        val ms:MyString = new MyString("bc");
        //val j_ix = j_s.contains(ms);			// java.lang.String API is not available
        //Console.OUT.println("Java 'abc'.contains(char sequence 'bc'): "+j_ix);
    }
}
