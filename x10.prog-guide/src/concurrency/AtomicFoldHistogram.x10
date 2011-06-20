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
 * histogram implementation using atomicity for the entire operation of folding
 * the partial results into final answer.
 */
public class AtomicFoldHistogram extends Histogram.PlainInt {
   public def this(input: Array[Int](1), min: Int, max: Int) {
      super(input, min, max);
   }
   public def computeResult(numAsyncs: Int): Long {
     val time = System.nanoTime();
      val sliceSize = input.size/numAsyncs;
      val lastAsync = numAsyncs - 1;
      finish {
         for (i in 0..lastAsync) async {
            val sliceStart = i * sliceSize;
         	val sliceEnd = (i==lastAsync) ? input.size-1 : sliceStart + sliceSize - 1;
         	val partial = new Array[Int](result.region, 0);
         	for (j in sliceStart..sliceEnd) partial(input(j))++;
         	atomic {
      			for (k in partial) this.result(k) += partial(k);
      		}
         }
      }
      return (System.nanoTime() - time);
   }
}
