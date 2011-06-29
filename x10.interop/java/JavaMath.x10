import x10.interop.Java;
public class JavaMath {
    public static def main(Array[String]) {
        val x:Double = 0.5;
        val pi:Double = Math.PI;
        val j_pi:Java.double = java.lang.Math.PI;
        val tpi:Double = Math.cos(pi);
        val j_tpi:Java.double = java.lang.Math.cos(Java.convert(pi));
        Console.OUT.println("X10 pi: "+pi+"\nJava pi: "+Java.convert(j_pi));
        Console.OUT.println("X10 tan(pi): "+tpi+"\nJava tan(pi): "+Java.convert(j_tpi));
    }
}
