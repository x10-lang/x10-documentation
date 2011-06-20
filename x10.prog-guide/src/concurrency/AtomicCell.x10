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
//START TeX: emptyfill
class AtomicCell {
   var full : Boolean;
   var contents : Int;
   
   def this() { full = false; contents = 0xdeadbeef; }
   def this(init:Int) {full = true; contents = init;}
   
   def fill(newVal:Int) {// \xlref{emptyfill-fill}
     when(!full) {
       full = true; contents = newVal;// \xlref{emptyfill-setcontents}
     }
   }// \xlref{emptyfill-endfill}
   def empty(): Int {// \xlref{emptyfill-empty}
     when(full) { full = false; return contents; }
   }// \xlref{emptyfill-endempty}
//END TeX: emptyfill
//START TeX: main
   public static def main(Array[String](1)){
      val c = new AtomicCell(0);
      async for([i] in 1 .. 10) c.fill(10*i);
      async for([j] in 1..10) {
         Console.OUT.println("value "+j + " is " + c.empty());
      }
   }
//END TeX: main
}
