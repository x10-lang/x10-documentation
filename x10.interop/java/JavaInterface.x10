import x10.interop.Java;
public class JavaInterface {
    public static class MyString(s:String) implements java.lang.CharSequence {
        def charAt(index:Java.int):Java.char {
            return s(index);
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
        val j_s:String = "abc";
        val ms:MyString = new MyString("bc");
        val j_ix:Java.int = j_s.indexOf(ms); // invalid (not exposed)
        Console.OUT.println("Java 'abc'.indexOf('bc'): "+j_ix);
    }
}
