 package expres.sio.nsca.lls;
class Callsome {
  static val closure = () => 1;
  static def method () = 2;
  static val closureEvaluated = Callsome.closure();
  static val methodEvaluated = Callsome.method();
}
