import x10.interop.Java;
public class JavaGeneric {
    val f: Any;
    public def this(v: Any) { this.f = v; }
    public def toString() = this.f.toString();
    public static def main(Array[String]) {
        val x:java.util.List[JavaGeneric] = new java.util.ArrayList[JavaGeneric]();
        x.add(new JavaGeneric(3));
        x.add(new JavaGeneric("4"));
        x.add(new JavaGeneric(5.0));
        for (val i: java.util.Iterator[JavaGeneric] = x.iterator(); i.hasNext(); ) {
            val e: JavaGeneric = i.next();
            Console.OUT.println(e.toString());
        }
        for (e: JavaGeneric in x) { // if we extend for loops to support java.util.Iterable[T]
            Console.OUT.println(e.toString());
        }
    }
}
