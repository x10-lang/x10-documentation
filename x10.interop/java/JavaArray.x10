import x10.interop.Java;
public class JavaArray {
    public static def main(Array[String]) {
        val v:Java.array[java.lang.Object] = new Java.array[java.lang.String](10);
        val u:Java.array[Java.array[java.lang.Object]] = Java.newArray[java.lang.String](10,20);
        val w:java.lang.Object = Java.convert("3");
        java.util.Arrays.fill(v, w);
        Console.OUT.println("Java: "+Java.convert(v(0) as java.lang.String));
    }
}
