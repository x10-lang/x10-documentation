import x10.interop.Java;
public class JavaArray2 {
    public static def main(Array[String]) {
        val v:Array[Int](1) = [1, 2, 3];
        val j_v:Java.array[Int] = Java.convert(v);
        val w:Array[Int](1) = Java.convert(j_v);
        Console.OUT.println("X10 size: "+v.size);
        Console.OUT.println("Java length: "+j_v.length);
        Console.OUT.println("Java->X10 size: "+w.size);
        Console.OUT.println("X10 elem: "+v(0));
        Console.OUT.println("Java elem: "+j_v(0));
        Console.OUT.println("Java->X10 elem: "+w(0));
    }
}
