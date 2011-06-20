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
//START TeX: ait
public class AtomicInc {
	public static def main(args: Array[String]) {
	   var n : Int = 0;
	   finish for (var m: Int = 0; m<2; m++) {
	      async for(var k: Int = 0; k<10000; k++) atomic n++; //\xlref{ait}{async1}
	   }
	   Console.OUT.println("n is "+n);
	}
}
//END TeX: ait
