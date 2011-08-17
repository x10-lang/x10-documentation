class Fig1 {
    // 1-- keep going, 2 -- true, 3-- false
    static def parallelOr(a:()=>Int, b:()=>Int):Boolean {
        val done=new Cell[Boolean](false);
        finish {
            async {
                var aa:Int=1;
                var cont:Boolean=true;
                for (; aa==1 && cont; aa=a()) {
                    atomic cont = ! done();
                }
                if (aa==2)
                    atomic done()=true;
            }
            async {
                var aa:Int=a();
                var cont:Boolean=true;                
                for (; aa==1 && cont; aa=b()) {
                    atomic cont = !done();
                }
                if (aa==2)
                    atomic done()=true;
            }
        }
        return done();
    }
    static def h()=true;
    public static def main(array: Array[String]) {
        val a = Int.parseInt(array(0));
        val b = Int.parseInt(array(1));        
        val x=():Int=>a; 
        val y=():Int=>b;
        Console.OUT.println(parallelOr(x,y));
    }
}