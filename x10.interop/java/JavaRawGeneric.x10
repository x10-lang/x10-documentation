import x10.interop.Java;
public class JavaRawGeneric {
    val f: Any;
    public def this(v: Any) { this.f = v; }
    public def toString() = this.f.toString();
    public static def main(Array[String]) {
        val x:java.util.List = new java.util.ArrayList();
        x.add(new JavaRawGeneric(3));
        x.add(new JavaRawGeneric("4"));
        x.add(new JavaRawGeneric(5.0));
        for (val i: java.util.Iterator = x.iterator(); i.hasNext(); ) {
            val e: JavaRawGeneric = i.next() as JavaRawGeneric;
            Console.OUT.println(e.toString());
        }
        //for (e: JavaRawGeneric in x) { // not possible if we use erased types
        //    Console.OUT.println(e.toString());
        //}
    }
}
