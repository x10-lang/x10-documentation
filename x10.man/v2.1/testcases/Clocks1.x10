package Clocks.For.Spock;
class ClockEx {
  static def say(s:String) =
 { /*atomic{x10.io.Console.OUT.println(s);}*/ }
  public static def main(argv:Rail[String]) {
    finish async{
      val cl = Clock.make();
      async clocked(cl) {// Activity A
        say("A-1");
        next;
        say("A-2");
        next;
        say("A-3");
      }// Activity A

      async clocked(cl) {// Activity B
        say("B-1");
        next;
        say("B-2");
        next;
        say("B-3");
      }// Activity B
    }
  }
 }