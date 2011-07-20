import x10.interop.Java;
public class JavaInterface {
    public static class MyString(s:String) implements java.lang.CharSequence { // it's okay to implement java interface
        def charAt(index:Int):Char {
            return s(index);
        }
        def length():Int {
            return s.length();
        }
        def subSequence(start:Int, end:Int):java.lang.CharSequence {
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
