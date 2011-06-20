import x10.util.concurrent.AtomicInteger;

public class AtomicIntInc {
    public static def main(args: Array[String]) {
//START TeX: aiit
       val n = new AtomicInteger(0); //\xlref{aiit-n}
       finish for (var m: Int = 0; m<2; m++) {
           async for(var k: Int = 0; k<10000; k++) n.getAndAdd(1); // \xlref{aiit-async}
       }
       Console.OUT.println("n is "+n.get());
//END TeX: aiit
    }
}
