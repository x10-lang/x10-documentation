import x10.interop.Java;
public class X10GenericViaJava {
    public static class Generic[T] {
        // This will be referenced from the Java class X10GenericViaJava_J.Client
        private val x:T;
        public def this(v:T) { this.x = v; }
        public operator this() = x;
    }
    public static def main(Array[String]) {
        // Comment out the following 4 lines and uncomment the next 3 for bootstrapping
        val v:X10GenericViaJava_J.Client = new X10GenericViaJava_J.Client();
        val i:Generic[Int] = v.getIntG();
        val d:Generic[Double] = v.getDoubleG();
        val o:Generic[Object] = v.getObjectG();
        //val i:Generic[Int] = new Generic[Int](3);
        //val d:Generic[Double] = new Generic[Double](4.0);
        //val o:Generic[Object] = new Generic[Object](new x10.util.Box(5));
        Console.OUT.println("Java-created int: "+i());
        Console.OUT.println("Java-created double: "+d());
        Console.OUT.println("Java-created object: "+o());
    }
}
