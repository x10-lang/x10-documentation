class Fig2 {
    static val CONT=1;
    static val TRUE=2;
    static val FALSE=3;
    static def run(done:Cell[Boolean], a:()=>Int) {
        var aa:Int=a();
        var cont:Boolean=true;         
        for (; aa==CONT && cont;aa=a()) {
            atomic cont = !done();  
        }
        if (aa==TRUE)
            atomic done()=true;
    }
    static def parallelOr(a:()=>Int, b:()=>Int):Boolean {
        val done=new Cell[Boolean](false);
        finish {
            async {
                var aa:Int=a();
                var cont:Boolean=true;         
                for (; aa==CONT && cont;aa=a()) {
                    atomic cont = !done();  
                }
                if (aa==TRUE)
                    atomic done()=true;
            }
            async {
                var aa:Int=a();
                var cont:Boolean=true;         
                for (; aa==CONT && cont;aa=b()) {
                    atomic cont = !done();  
                }
                if (aa==TRUE)
                    atomic done()=true;
                
            }
        }
        return done();
    }
    static def h()=true;
    public static def main(array: Array[String]) {
        val a = Int.parseInt(array(0));
        val b = Int.parseInt(array(1));        
        Console.OUT.println(parallelOr(():Int=>a, ():Int=>b));
    }
}