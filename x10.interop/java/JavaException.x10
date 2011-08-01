public class JavaException {
    static class A implements JavaExceptionIntf {
        public def f():void {}
        public def g():void {}
    }
    static def testa() {
        val a = new A();
        a.f(); // should be OK
        a.g(); // should be OK
    }
    // static def testi() { // should be type check error
    //     val i:JavaExceptionIntf = new A();
    //     i.f(); // should be OK
    //     i.g(); // throws java.lang.Throwable
    // }

    // static def test1():java.io.File { // should be type check error
    //     return java.io.File.createTempFile("temp", null);
    // }
    // X10 frontend should allow throwing/catching all subtypes of java.lang.Throwable.
    // $ x10c -cp . JavaException.x10
    // JavaException.x10:28: Can only throw subclasses of "x10.lang.Throwable".
    static def test2():java.io.File { // should be OK
        var f:java.io.File = null;
        try {
            f = java.io.File.createTempFile("temp", null);
        } catch (e:java.io.IOException) {
        }
        return f;
    }
    @Throws("java.io.IOException") static def test3():java.io.File { // should be OK
        return java.io.File.createTempFile("temp", null);
    }
    // static def test4():java.io.File { // should be type check error
    //     return test3();
    // }
    // static def test5():java.io.File { // should be type check error
    //     val f = new java.io.File("foo.txt");
    //     return f.createNewFile();
    // }
}
