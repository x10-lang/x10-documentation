public class X10GenericViaJava_J {
    public static class Client {
        public X10GenericViaJava.Generic<x10.core.Int> getIntG() {
            return X10GenericViaJava.Generic.$make(x10.core.Int.$RTT, x10.core.Int.$box(3), (java.lang.Class<?>)null);
        }
        public X10GenericViaJava.Generic<x10.core.Double> getDoubleG() {
            return X10GenericViaJava.Generic.$make(x10.core.Double.$RTT, x10.core.Double.$box(4.0), (java.lang.Class<?>)null);
        }
        public X10GenericViaJava.Generic<x10.core.RefI> getObjectG() {
            return X10GenericViaJava.Generic.$make(x10.rtt.Types.OBJECT, x10.util.Box.$make(x10.rtt.Types.INT, x10.core.Int.$box(5), (java.lang.Class<?>)null), (java.lang.Class<?>)null);
        }
    }
}
