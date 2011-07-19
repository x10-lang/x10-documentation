import x10.interop.Java;
public class JavaField {
    //val f1:java.lang.Object = null;		// impossible to refer to java.lang.Object type
    //val f2:Any = new java.lang.Object();	// impossible to refer to java.lang.Object class
    public val f : Any = "any";
    public static def main(Array[String]) {
        val o = new JavaField();
        finish {
            async {
                Console.OUT.println("Waiting");
                //o.f.wait();						// impossible
                Console.OUT.println("Done");
            }
            async {
                Runtime.sleep(100);
                Console.OUT.println("Notifying");
                //o.f.notifyAll();					// impossible
            }
        }
    }
}
