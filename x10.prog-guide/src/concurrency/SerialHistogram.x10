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
 * Straightforward serial implementation of a histogram
 */
public class SerialHistogram extends Histogram.PlainInt {
   public def this(input: Array[Int](1), min: Int, max: Int) {
      super(input, min, max);
   }
   
   public def computeResult(): Long {
      val firstIn = input.region.min(0);
      val lastIn  = input.region.max(0);
      val time = System.nanoTime();
      //START X10: computeResult
      for (i in input) result(input(i))++; 
      //END X10: computeResult
      return (System.nanoTime()-time);
   }
}
