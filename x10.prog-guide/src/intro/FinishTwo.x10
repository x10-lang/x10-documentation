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

public class FinishTwo {
  static def do_this(){}
  static def do_that(){}
  public static def main(argv:Array[String](1)) {
//START TeX: finishtwo
      finish {
        async do_this();
        async do_that();
      }
//END TeX: finishtwo
  }
}
