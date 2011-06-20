//START TeX: diesel
  public class DieselShip extends Ship {
    public val fuelTankCapacity: Double; // in gallons
    public var gallonsRemaining: Double;
    
    public def this(name:String, maxPsgrs:Int, tankSize:Double) {
       super(name, maxPsgrs);
       fuelTankCapacity = gallonsRemaining = tankSize;
    }
    public def throwOverboard(name: String, why: String) {
      super.throwOverboard(name, why);
      /* more stuff here */
    }
    /* ... more methods can go here */
 }
//END TeX: diesel
