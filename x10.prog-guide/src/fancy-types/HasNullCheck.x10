import x10.util.*;

public class HasNullCheck {
  /** A very puny Person class indeed, but enough for our example.
  */
  static class Person {
    // A more reasonable program would let different people 
    // have different phone numbers. 
    def phoneNumber() = 123456789L; 
  }

//START TeX: hasnullcheckDB
  static val db = new HashMap[String, Person{self!=null}]();
  static def lookUpOrCreate(name:String) : Person{self!=null} = {
    if( db.containsKey(name)) {
       return db.getOrThrow(name) ;
    }
    val p = new Person(); // \xlref{hasnullcheckDB-ctor}
    db.put(name, p);
    return p;
  }
//END TeX: hasnullcheckDB
  public static def main(argv:Array[String](1)) {
//START TeX: hasnullcheck
    val x : Person{self!=null} = lookUpOrCreate("Kim Geep");
    Console.OUT.println("Kim's phone number is " + x.phoneNumber());
//END TeX: hasnullcheck
  }
}
