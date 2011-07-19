import x10.interop.Java;
public class JavaField {
    public val f:java.util.concurrent.locks.Lock = new java.util.concurrent.locks.ReentrantLock();
    public static def main(Array[String]) {
        val o = new JavaField();
        finish {
            async {
                Runtime.sleep(10);
                Console.OUT.println("Waiting");
                o.f.lock();
                Console.OUT.println("Done");
                o.f.unlock();
            }
            async {
                o.f.lock();
                Runtime.sleep(100);
                Console.OUT.println("Notifying");
                o.f.unlock();
            }
        }
    }
}
