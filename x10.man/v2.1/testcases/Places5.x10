package Places.Are.For.Graces;;
abstract class Thing {}
class DoMine {
  static def dealWith(Thing) {}
  public static def dealWithLocal(things: Rail[Thing]) {
/*
     THIS EXAMPLE MUST BE UPDATED.
     for(thing in things) {
    	 if (thing.home == here)
            dealWith(thing);
     }
*/
  }
}