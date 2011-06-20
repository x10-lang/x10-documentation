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
 * common functionality for histograms built using an Int result array.
 */
public class IntHistogram extends Histogram {
   val result: Array[Int](1);
   public def this(data: Array[Int](1), min: Int, max: Int) {
      super(data, min, max);
      this.result = new Array[Int](min..max, 0);
   }
   public def apply(i: Int) = this.result(i);
   public def clear() {
      for([i] in minDataValue..maxDataValue) result(i) = 0;
   }
   public def check(sh: SerialHistogram, who: String) {
      var errorsToShow: Int = 5;
      var errorsSeen: Int = 0;
      for (i in minDataValue..maxDataValue) {
         if (result(i) != sh(i)) {
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
