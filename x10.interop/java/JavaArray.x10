import x10.interop.Java;
public class JavaArray {
    public static def main(Array[String]) {
        val v:Java.array[java.lang.Number] = new Java.array[java.lang.Integer](10);
        val u:Java.array[Java.array[java.lang.Number]] = Java.newArray[java.lang.Integer](10,20);
        val w:java.lang.Number = new java.lang.Integer(3);
        java.util.Arrays.fill(v, w);
        Console.OUT.println("Java: "+v(0) as java.lang.Integer);
        val x:Java.array[Java.int] = new Java.array[Java.int](3);
        //val y:Java.array[Any] = x; // produces a compile-time error
        java.util.Arrays.fill(x, 7);
        Console.OUT.println("Java: "+x(0));
    }
}
