import x10.interop.Java;
public class JavaField {
    public val f:java.lang.Object = new java.lang.Object();
    public static def main(Array[String]) {
        val o = new JavaField();
        finish {
            async {
                Console.OUT.println("Waiting");
                o.f.wait();
                Console.OUT.println("Done");
            }
            async {
                Runtime.sleep(100);
                Console.OUT.println("Notifying");
                o.f.notifyAll();
            }
        }
    }
}
