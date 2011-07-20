import x10.interop.Java;
public class JavaArray {
    public static def main(Array[String]) {
        val v:Java.array[java.lang.Number] = new Java.array[java.lang.Integer](10);
        val u:Java.array[Java.array[java.lang.Number]] = Java.newArray[java.lang.Integer](10,20);
        val w:java.lang.Number = 3 as java.lang.Integer;
        java.util.Arrays.fill(v, w);
        Console.OUT.println("Java: "+v(0) as java.lang.Integer);
    }
}
