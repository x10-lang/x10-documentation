class IndirectAsyncs{
//START TeX: indasyncs
   var a:Boolean = false, b:Boolean = false, c:Boolean = false;
   def spawnAsyncs() { 
      async {a = true;}
      async {b = true;} 
   }
   def nestAsyncs() {
     finish { 
        async  spawnAsyncs();// \xlref{indasyncs-async3}
       async { c = true; }
     }// \xlref{indasyncs-endfinish}
     assert a && b && c;
   }
//END TeX: indasyncs
}
