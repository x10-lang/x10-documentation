public class MontyPi {
    public static def pi(N:Int):Double {
        val ans = new Acc[Double](Double.Sum);
        finish for (p in Dist.makeUnique()) async at(p) {
            val r = new Random();
            var result:double=0.0D;
            for(c in 1..N) {
                val x = r.nextDouble();
                val y = r.nextDouble();
                if (x*x +y*y <= 1.0) result++;
            }                
            result <- result;    
            }
        return 4*ans()/(N*Place.MAX_PLACES);
    }
}
