import x10.interop.Java;
public class JavaInterface2 {
    public static interface Measurable[T] {
        public def length():T;
    }
    public static class MyString(s:String) implements java.lang.CharSequence, Measurable[Int] {
        public def charAt(index:Java.int):Java.char {
            return s(index);
        }
        public def length():Java.int {
            return s.length();
        }
        public def subSequence(start:Java.int, end:Java.int):java.lang.CharSequence {
            return new MyString(s.substring(start, end));
        }
        public def toString():String {
            return s;
        }
    }
    public static def main(Array[String]) {
        val j_s:java.lang.StringBuffer = new java.lang.StringBuffer("abc");
        val ms:MyString = new MyString("bc");
        j_s.append(ms);
        Console.OUT.println("Java 'abc'.append('bc'): "+j_s);
        val mr:Measurable[Int] = ms;
        Console.OUT.println("'bc'.length(): "+mr.length());
    }
}
