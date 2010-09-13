 package expres.sio.nsca.lls.twoooo;
 class Callsome {static val closure = () => 1; static def method () = 2; static val methodEvaluated = Callsome.method();
  static def closure () = 3;
  // ERROR: static errory = Callsome.closure();
 }