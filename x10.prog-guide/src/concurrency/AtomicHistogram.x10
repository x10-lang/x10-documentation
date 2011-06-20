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
 * Histogram implementation with an atomic guard on each update of a
 * slot in the result array.
 */
public class AtomicHistogram extends Histogram.PlainInt {
   public def this(data: Array[Int](1), min: Int, max: Int) {
      super(data, min, max);
   }
   //START TeX: computeResult
   public def computeResult(numAsyncs: Int): Long {
      val time = System.nanoTime();
      val sliceSize = input.size/numAsyncs;
      val lastAsync = numAsyncs-1;
      finish {
         for (i in 0..lastAsync) {
		      val sliceStart = i * sliceSize;
			   val sliceEnd = (i==lastAsync) ? (input.size-1) : (sliceStart+sliceSize-1);
            async {
               val partial = new Array[Int](result.region, 0);
               for (j in sliceStart..sliceEnd) partial(input(j))++;
               for (j in partial) {
                  atomic this.result(j) += partial(j);
            	}
            }
         }
      }
      return (System.nanoTime() - time);
   }
   //END TeX: computeResult
}
