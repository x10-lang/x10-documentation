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
 * Example of using '<:' in declarations to give partial information
 */
//START TeX: argvpartial
public class ArgvPartialInfo {
    public static def main(s: Array[String](1)) {// \xlref{argvpartial-s}
        val a <: Object = s; // \xlref{argvpartial-a}
        val b <: Array[String] = s;// \xlref{argvpartial-b}
        val c <: Array[String]{rank != 3} = s;// \xlref{argvpartial-c}
    }
}
//END TeX: argvpartial
