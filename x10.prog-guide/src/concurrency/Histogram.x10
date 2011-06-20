import x10.util.Random;
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
 * We use computing histograms as an illustration of various uses of atomic
 * versus AtomicInteger and the like.  We've built this on code by Martha Kim
 * written as part of a course taught by Vijay Saraswat in the Fall of 2009
 * at Columbia University.
 */
public class Histogram {
   /** 
    * the limits for the data values are the limits for the result
    * array's index
    */
   public val maxDataValue: Int;
   public val minDataValue: Int;
   /**
    * the input array is assumed for simplicity to be indexed from 0 to
    * input.size-1.
    */
   public val input:  Array[Int](1);

   public def this(data: Array[Int](1), min: Int, max: Int) {
      this.input = data;
      this.minDataValue = min;
      this.maxDataValue = max;
   }
   
   public def computeResult(): Long {
      throw new UnsupportedOperationException("Subclass must implement.");
   }
      
   public def clear()  {
      throw new UnsupportedOperationException("Subclass must implement.");
   }
   public def histogramForSlice(firstIn: Int, lastIn: Int) {
      val r = (minDataValue..maxDataValue) as Region(1);
      val result = new Array[Int](r, 0);
      for (i in firstIn..lastIn) result(input(i))++;
      return result;
   }

   /** top level class for histograms using Int-value result arrays */
   public static class PlainInt extends Histogram {
      /** the result array's values are Ints, as opposed to AtomicIntegers */
      public val result: Array[Int](1);
      
      public def this(data: Array[Int](1), min: Int, max: Int) {
         super(data, min, max);
         this.result = new Array[Int](min..max, 0);
      }
      
      public operator this(i: Int) = this.result(i);
      public operator this(i: Point(1)) = this.result(i);
      
      public def clear() { for(i in result) result(i) = 0; }
      
      protected def check(sh: SerialHistogram, who: String) {
         var errorsToShow: Int = 5;
         var errorsSeen: Int = 0;
         for (i in result) {
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
   
   public static def createInput(input: Array[Int](1), min: Int, max: Int) {
      val start = System.nanoTime();
      val rand = new Random();
      var nextValue: Int;
      val limit = max+1;
      val bottom = min-1;
      for(i in input) {
         nextValue = rand.nextInt(limit);
         while(nextValue <= 0) nextValue = rand.nextInt(limit);
         input(i) = nextValue + bottom;
      }
      return System.nanoTime() - start;
   }
   public static USAGE =
       "Usage: Histogram -in <input item count>\r\n"
       + "  -max <max data value>\r\n"
       + "  -min <min data value>\r\n"
       + "  -asy <number of asyncs>\r\n"
       + "  -reps<number of invocations>"
       + "Defaults are: size 1Meg, min 0, max 128K, asy 4, reps 10\r\n";
    /**   
     *  Main method 
     */  
    public static def main(args:Array[String](1)) {
       var inputSize: Int = 1024*1024;
       var minValue: Int = 0;
       var maxValue: Int = 128*1024;
       var asyncCount: Int = 4;
       var repetitions: Int = 10;
       var i: Int = 0;
       while(i < args.size) {
          val keyI = args(i++);
          val valueI = Int.parse(args(i++));
          if      (keyI.equals("-in")) inputSize = valueI;
          else if (keyI.equals("-max")) maxValue = valueI;
          else if (keyI.equals("-min")) minValue = valueI;
          else if (keyI.equals("-asy")) asyncCount = valueI;
          else if (keyI.equals("-reps")) repetitions = valueI;
          else {
             Console.ERR.println(USAGE);
             return;
          }
       }
       Console.OUT.println("Parameters are:\r\n\tinput count: "
             + inputSize + "\r\n\tmin: "
             + minValue + "\r\n\tmax: "
             + maxValue + "\r\n\tasyncs: "
             + asyncCount + "\r\n\treps: " 
             + repetitions);

       val input = new Array[Int](inputSize);
       val populateTime = createInput(input, minValue, maxValue);
       var serialTime:     Long = 0;
       var rangeSplitTime: Long = 0;
       var atomicTime:     Long = 0;
       var atomicFoldTime: Long = 0;
       var atomicIntTime:  Long = 0;
       val sh  = new SerialHistogram(input, minValue, maxValue);
       val rsh = new RangeSplitHistogram(input, minValue, maxValue);
       val ah  = new AtomicHistogram(input, minValue, maxValue);
       val afh = new AtomicFoldHistogram(input, minValue, maxValue);
       val aih = new AtomicIntHistogram(input, minValue, maxValue);
       var errors: Int = 0;
       for(rep in 1..repetitions) {
          serialTime     += sh.computeResult();
          rangeSplitTime += rsh.computeResult(asyncCount);
          atomicTime     += ah.computeResult(asyncCount);
          atomicFoldTime += afh.computeResult(asyncCount);
          atomicIntTime  += aih.computeResult(asyncCount);
          errors += rsh.check(sh, "Range split" );
          errors += ah.check(sh, "Atomic per value" );
          errors += afh.check(sh, "Atomic fold" );
          errors += aih.check(sh, "AtomicInteger" );
          if (errors > 0) break;
          sh.clear();
          ah.clear();
          rsh.clear();
          afh.clear();
          aih.clear();
       }
       val M = 1000*1000;  // convert nanoseconds to milliseconds
       if (errors == 0) Console.OUT.println(
          "For " + repetitions + " trials, total times were:\r\n\t" 
	 			+ populateTime/M   + " to populate the input,\r\n\t" 
	 			+ serialTime/M     + " to compute serially\r\n\t"
	 			+ rangeSplitTime/M + " to compute splitting the range\r\n\t"
         	+ atomicTime/M     + " to compute atomically on each data value\r\n\t"	    
         	+ atomicFoldTime/M + " to compute fold atomically\r\n\t"	    
         	+ atomicIntTime/M  + " to compute using AtomicInteger\r\n");    
   }
}
