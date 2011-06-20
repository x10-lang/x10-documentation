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
//START TeX: hello
//TeX: Copyright 1977 Greeter's Anonymous. All rights reserved \xlref{hello-cmnt}
/** classic first code example */ //TeX YES: \xlref{hello-x10doc1}
public class HelloWorld { //\xlref{hello-code0}
   /** //TeX:
    * writes "Hello, World" to the console //TeX YES: 
    * @param args the command line arguments //TeX YES: \xlref{hello-x10doc2}
    */ //TeX:
   public static def main(args:Array[String](1)) { //\xlref{hello-code1}
      x10.io.Console.OUT.println("Hello, World"); //\xlref{hello-code2}
   }
}
//END TeX: hello
