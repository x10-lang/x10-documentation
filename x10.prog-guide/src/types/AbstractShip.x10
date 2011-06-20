//START TeX: absship
abstract public class AbstractShip {
    public static DEFAULT_SIZE = 500;// \xlref{absship-a}
    public  val name: String;// \xlref{absship-b}
    //TeX: and all the other code as from Ship.x10
//END TeX: absship

//START TeX: absshipabs
  public abstract def costPerPassengerMile(): Double;
//END TeX: absshipabs

    private var passengers: Array[String](1);// \xlref{absship-c}
    private var onBoard: Int = 0;// \xlref{absship-d}
    
    public def this(name: String) {// \xlref{absship-ctor}
       this(name, DEFAULT_SIZE);
    } 
    public def this(name:String, initialCapacity:Int) {
       this.name = name;  
       passengers = new Array[String](1..initialCapacity);
    }// \xlref{absship-endctor}

    static def resize(size:Int, na:AbstractShip) { /*...*/ }// \xlref{absship-resize}

    public def addPassenger(name: String) { /*...*/ }// \xlref{absship-defs}
    def throwOverboard(name: String, why: String) { /*...*/ }
    protected def showPassengers() { /*...*/ }// \xlref{absship-enddefs}
    
    public static def main(args: Array[String](1)) { /*...*/ } // \xlref{absship-main}
    
    static class FareClasses { /*...*/ }   // \xlref{absship-farecls}
    protected class Galley { // \xlref{absship-galley}
        private val platesPerPerson = 4;
        public def platesRequiredToday() {
           return AbstractShip.this.onBoard * this.platesPerPerson;// \xlref{absship-galleyplate}
        }
        def this(){}
     }
    private var galley : Galley = null ; // \xlref{absship-declgalley}
    public def galley() = this.galley; // \xlref{absship-getgalley}
    public def makeGalley() {
       this.galley = this.new Galley(); // \xlref{absship-newgalley}
    }

   }

