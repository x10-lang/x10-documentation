/*
 *  This file is part of the X10 project (http://x10-lang.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  (C) Copyright IBM Corporation 2010.
 */

/**
 * Print a "Hello, World" from every place
 */


//START TeX: hfep
public class HelloFromEveryPlace {
  public static def main(argv:Array[String](1)) {
    for(p in Place.places()) { //\xlref{hfep-for}
      at(p) {//\xlref{hfep-at}
        Console.OUT.println("Hello from " + here); //\xlref{hfep-out}
        assert here == p;//\xlref{hfep-assert}
      }
    }
  }
}
//END TeX: hfep


