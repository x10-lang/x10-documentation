interface Named {
   def name():String;
 }
 interface Mobile {
   def move(howFar:Int):Void;
 }
 interface Person extends Named, Mobile {}
 interface NamedPoint extends Named, Mobile{}
class KimThePoint implements Person {
   var pos : Int = 0;
   public def name() = "Kim (" + pos + ")";
   public def move(dPos:Int) { pos += dPos; }
}
