import x10.util.Random;
import x10.util.concurrent.*;

public class QueueDriver {
   val testSize: Int;
   val ops:  Array[Boolean](1);
   val copy: Array[Int](1);
   val nd:   NaiveQueue[Int];
   val cd:   CircularQueue[Int];
   val cx = new AtomicInteger(0);
   val newcx = new AtomicInteger(0);
   val newnx = new AtomicInteger(0);
   var nx: Int = 0;

   public def this(args: Array[String](1)) {
      testSize = (args.size > 0) ? Int.parse(args(0)) : 10000;
      val r = new Random();
      ops = new Array[Boolean](testSize, (Int)=>r.nextBoolean());
      copy = new Array[Int](testSize, 0);
      nd = new NaiveQueue[Int](7500);
      cd = new CircularQueue[Int](1250);
   }
   
   private def testND(id: Int) {
      var errs: Int = 0;
      val first = id*ops.size/2;
      val last  = first+ops.size/2;
      for(var n: Int = first; n<=last; n++) {
         try {
            if (ops(n)||id==3) {
               nd.addLast(newnx.addAndGet(1));
            }
            else {
               atomic {
                  val deleted = nd.removeFirst();
                  if (deleted == 0) errs++;
                  else {
                     copy(nx++) = deleted;
                     //Console.OUT.println(id+"."+n+" del "+deleted);
                  }
               }
            }
         }
         catch(e: Exception) {
            if (errs++ <=  10) Console.ERR.println("ND "+id+"."+n+": "+e);
         }
      }
      Console.OUT.println(id+": test ND complete: "+errs+" errors and "+nx+" deletions.");
   }
   
   private def testCD(id: Int) {
      var errs: Int = 0;
      val first = id*ops.size/3;
      val last  = first+ops.size/3;
      for(var n: Int = first; n<=last; n++) {
         try {
            if (ops(n) || id == 2) {
               cd.addLast(newcx.addAndGet(1));
               //Console.OUT.println(id+"."+n+": add "+data(n));
            }
            else {
                val deleted = cd.removeFirst();
                copy(cx.getAndAdd(1)) = deleted;
                //Console.OUT.println(id+"."+n+": del "+deleted);
            }
         }
         catch(e: Exception) {
            if (errs++ <=  10) Console.ERR.println("CD "+id+"."+n+": "+e);
         }
      }
      Console.OUT.println(id+": test CD complete: "+errs+" errors and "+cx+" deletions.");
   }
   
   public static def main(args: Array[String](1)) {
      val dd = new QueueDriver(args);
      val twoThreads =  (args.size > 1);
      finish {
         if (twoThreads) async dd.testND(1);
         dd.testND(2);
      }
      for(k in 0..(dd.nx-1)) {
         if (dd.copy(k) != dd.nd.buffer(k)) {
            Console.ERR.println("Got "+dd.copy(k)+": expected "+dd.nd.buffer(k));
         }
         Console.OUT.print(dd.copy(k)+"="+dd.nd.buffer(k)+(k%5 == 4? "\n" : ", "));
         dd.copy(k) = 0;
      }
      finish for(n in 0..2) {
         async dd.testCD(n);
      }
      for(k in 0..(dd.cx.get()-1)) {
         if (dd.copy(k) != k+1) {
            Console.ERR.println("Got "+dd.copy(k)+": expected "+(k+1));
         }
      }
   }
}