import x10.interop.Java;
public class JavaClass {
    public static class MyCollection(sz:Int) extends java.util.AbstractCollection {
        public def size():Int = sz;
        public def iterator():java.util.Iterator = new java.util.Iterator() {
            private var cnt:Int = 0;
            public def hasNext():Boolean = cnt < sz;
            public def next():Any = new java.lang.Integer(cnt++);
            public def remove():void { throw new java.lang.UnsupportedOperationException(); }
        };
    }
    public static def main(Array[String]) {
        val mc: java.util.Collection = new MyCollection(20);
        for (val i: java.util.Iterator = mc.iterator(); i.hasNext(); ) {
            val e: java.lang.Integer = i.next() as java.lang.Integer;
            Console.OUT.println(e.toString());
        }
    }
}
