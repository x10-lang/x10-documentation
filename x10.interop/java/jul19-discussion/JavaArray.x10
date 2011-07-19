import x10.interop.Java;
public class JavaArray {
    public static def main(Array[String]) {
        val v:Java.array[Any] = new Java.array[String](10);
        val u:Java.array[Java.array[Any]] = Java.newArray[java.lang.String](10,20);
        val w:Any = "3";
        java.util.Arrays.fill(v, w);
        Console.OUT.println("Java: "+v(0));
    }
}
