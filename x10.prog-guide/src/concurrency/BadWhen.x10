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
 * A VERY bounded queue: an atomic cell holds at most one Int.
 */
//START TeX: badwhen
class BadWhen {
   var pivot: Int = 0;
   
   public def turnOn() {
      when(pivot %2 == 1) Console.OUT.println("That's odd!");
   }
   
   public def tuneOut(n: Int) {
      pivot = n;
   }
   
   public static def main(Array[String](1)) {
      val bw = new BadWhen();
      async bw.turnOn();
      bw.tuneOut(1);
      bw.tuneOut(2);
   }
}
//END TeX: badwhen
