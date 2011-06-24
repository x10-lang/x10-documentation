public class NeedsNullCheck {
  /** A very puny Person class indeed, but enough for our example.
  */
  static class Person {
    // A more reasonable program would let different people 
    // have different phone numbers. 
    def phoneNumber() = 123456789L; 
  }
  static val BARD = new Person();
  /* Our database has only one person in it.
     Lookups of other people return null.
  */
  static def lookUp(name:String) =
    name.equals("Bard") ? BARD : null; 
  public static def main(argv:Array[String](1)) {
//START TeX: needsnullcheck
    val x : Person = lookUp("Kim Geep");
    Console.OUT.println("Kim's phone number is " + x.phoneNumber());
//END TeX: needsnullcheck
  }
}
