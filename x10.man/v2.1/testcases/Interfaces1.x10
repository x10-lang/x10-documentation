
interface Pushable(text:String, prio:Int) {
  def push(): Void;
  static val MAX_PRIO = 100;
}
class MessageButton(text:String, prio:Int)
  implements Pushable{self.prio==Pushable.MAX_PRIO} {
  public def push() {
    x10.io.Console.OUT.println(text + " pushed");
  }
}
