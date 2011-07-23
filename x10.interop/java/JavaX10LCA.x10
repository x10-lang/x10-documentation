import x10.interop.Java;
public class JavaX10LCA {
    public static class MyString(s:String) implements java.lang.CharSequence {
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
    public static def typeToString[T](x:T) {
        val a = new Array[T](0, x);
        val s = a.typeName();
        return s.substring(s.indexOf("["), s.lastIndexOf("]"));
    }
    public static def main(Array[String]) {
        val j_s:java.lang.StringBuffer = new java.lang.StringBuffer("abc");
        val ms:MyString = new MyString("bc");
        val lca = false ? j_s : ms;
        Console.OUT.println("LCA(java.lang.StringBuffer,MyString): "+typeToString(lca));
        val lca2 = false ? j_s : new Object();
        Console.OUT.println("LCA(java.lang.StringBuffer,x10.lang.Object): "+typeToString(lca2));
    }
}
