import x10.util.concurrent.AtomicInteger;
/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to you under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */
/**
 * Histogram built using an array of AtomicIntegers rather than Ints
 */
public class AtomicIntHistogram extends Histogram {
   val result: Array[AtomicInteger](1);
   public def this(input: Array[Int](1), min: Int, max: Int) {
      super(input, min, max);
      this.result = new Array[AtomicInteger]((min..max) as Region(1), (Point(1))=>new AtomicInteger(0));
   }
   
   public operator this(i: Int) = this.result(i).get();
   public operator this(i: Point(1)) = this.result(i).get();
   
   public def computeResult(numAsyncs: Int): Long {
      val time = System.nanoTime();
      val sliceSize = input.size/numAsyncs;
      val lastAsync = numAsyncs-1;
      finish {
         for (i in 0..lastAsync) {
            val sliceStart = i * sliceSize;
            val sliceEnd = i==lastAsync ? input.size-1 : sliceStart+sliceSize-1;
            async {
               val partial = new Array[Int](result.region, 0);
               for(j in sliceStart..sliceEnd) partial(input(j))++;
               for (j in partial) {
                  this.result(j).addAndGet(partial(j));
               }
            }
      	}
      }
      return (System.nanoTime() - time);
   }

   public def clear() {
      for(i in result) result(i).set(0);
   }
         
   public def check(sh: SerialHistogram, who: String) {
      var errorsToShow: Int = 5;
      var errorsSeen: Int = 0;
      for (i in result) {
         if (result(i).get() != sh(i)) {
            errorsSeen++;
            if (--errorsToShow >= 0) {
               Console.OUT.println("Incorrect count for " + who
                     + " at " + i + ": expected " + sh(i)
                     + ", found " + result(i));
            }
         }
      }
      return errorsSeen;
   }
}
