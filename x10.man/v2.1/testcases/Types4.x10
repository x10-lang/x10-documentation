package Types.For.Snipes.Interfaces;
interface Named {
  def name():String;
}
interface Mobile {
  def move(howFar:Int):Void;
}
interface Person extends Named, Mobile {}
interface NamedPoint extends Named, Mobile{}
