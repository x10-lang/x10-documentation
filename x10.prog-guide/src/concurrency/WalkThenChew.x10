/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2006-2010.
 */
/**
 * Synchronous use of "at(p)".  No concurrency.
 */
public class WalkThenChew {
   public static def bigComputation(first: Int, second: Int) {
      var a: String = "a";
      var b: String = "b";
      var answer: String = "";
      for(var m: Int = 0; m < first; m++) {
         answer += a;
         for(var n: Int =0; n< second; n++) {
            answer += b;
         }
      }
      return answer;
   }
   public static def main(args: Array[String](1)) {
      var big1: String = at(Place.place(0)) bigComputation(200,200);
      var big2: String = at(Place.place(0)) bigComputation(200,200);
      assert big1.equals(big2);
   }
}
