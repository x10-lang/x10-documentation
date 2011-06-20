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
 * If you split the range, rather than the input array, you don't need
 * any atomicity: each async hits its own subarray of the result array
 */  
public class RangeSplitHistogram extends Histogram.PlainInt {
   public def this(input: Array[Int](1), min: Int, max: Int) {
      super(input, min, max);
   }
   public def computeResult(numAsyncs: Int): Long {
      val time = System.nanoTime();   
   	val rangeChunk = (maxDataValue - minDataValue)/numAsyncs;
   	val lastAsync = numAsyncs - 1;
   	var first: Int = minDataValue;
   	finish {
   	   for(i in 0..lastAsync) {
   	      val last  = i<lastAsync  ? first+rangeChunk-1 : maxDataValue;
   	      async {
   	         for(j in input) {
	   	         val inputJ = input(j);
	   	         if (first <= inputJ && inputJ <= last) result(inputJ)++; 
	   	      }
	   	      first += rangeChunk;
   	      }
   	   }
   	}
   	return (System.nanoTime() - time);
   }
}
