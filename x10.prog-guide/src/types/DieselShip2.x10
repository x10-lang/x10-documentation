public class DieselShip2 extends AbstractShip {
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
//START TeX: costPerPassengerMile
  public def costPerPassengerMile(): Double = 0.018;
//END TeX: costPerPassengerMile
 }

