import x10.interop.Java;
public class JavaMath {
    public static def main(Array[String]) {
        val pi:Double = Math.PI;
        val j_pi:Java.double = java.lang.Math.PI;
        val tpi:Double = Math.cos(pi);
        val j_tpi:Java.double = java.lang.Math.cos(pi);
        Console.OUT.println("X10 pi: "+pi+"\nJava pi: "+j_pi);
        Console.OUT.println("X10 cos(pi): "+tpi+"\nJava cos(pi): "+j_tpi);
    }
}
