 package Functions.Are.For.Spunctions;
 class Examplllll {
 static
val sq: (Int) => Int
      = (n:Int) => {
           var s : Int = 0;
           val abs_n = n < 0 ? -n : n;
           for ([i] in 1..abs_n) s += abs_n;
           s
        };
}