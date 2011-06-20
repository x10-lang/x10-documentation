class NestAsyncs{
//START TeX: nestasyncs
   var a:Boolean = false, b:Boolean = false, c:Boolean = false;
   def nestAsyncs() {
    finish { // \xlref{nestasyncs-finish}
        async {// \xlref{nestasyncs-async1}
          async { a = true; } // \xlref{nestasyncs-async2}
          async { b = true; }// \xlref{nestasyncs-async3}
        }
        async { c = true; }// \xlref{nestasyncs-async5}
     }
     assert a && b && c;// \xlref{nestasyncs-assert}
  }// \xlref{nestasyncs-endfinish}

//END TeX: nestasyncs
}
