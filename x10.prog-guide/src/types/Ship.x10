//START TeX: ship
public class Ship {
    public static DEFAULT_SIZE = 500;// \xlref{ship-a}
    public  val name: String;// \xlref{ship-b}
    private var passengers: Array[String](1);// \xlref{ship-c}
    private var onBoard: Int = 0;// \xlref{ship-d}
    
    public def this(name: String) {// \xlref{ship-ctor}
       this(name, DEFAULT_SIZE);
    } 
    public def this(name:String, initialCapacity:Int) {
       this.name = name;  
       passengers = new Array[String](1..initialCapacity);
    }// \xlref{ship-endctor}

    static def resize(size:Int, na:Ship) { /*...*/ }// \xlref{ship-resize}

    public def addPassenger(name: String) { /*...*/ }// \xlref{ship-defs}
    def throwOverboard(name: String, why: String) { /*...*/ }
    protected def showPassengers() { /*...*/ }// \xlref{ship-enddefs}
    
    public static def main(args: Array[String](1)) { /*...*/ } // \xlref{ship-main}
    
    static class FareClasses { /*...*/ }   // \xlref{ship-farecls}
    protected class Galley { // \xlref{ship-galley}
        private val platesPerPerson = 4;
        public def platesRequiredToday() {
           return Ship.this.onBoard * this.platesPerPerson;// \xlref{ship-galleyplate}
        }
        def this(){}
     }
    private var galley : Galley = null ; // \xlref{ship-declgalley}
    public def galley() = this.galley; // \xlref{ship-getgalley}
    public def makeGalley() {
       this.galley = this.new Galley(); // \xlref{ship-newgalley}
    }

   }
//END TeX: ship
