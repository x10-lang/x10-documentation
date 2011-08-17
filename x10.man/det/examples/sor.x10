//Sor - Parallel
for ([p] in 1..numIter) 
    for ([o] in 0..1) 
        finish for ([ii] in 0..(((M-2-(1+o))/2))) async {
            val i = 2 * ii + 1 + o;
            for ([j] in 1..(N-2)) 
                G(i, j) = omega_over_four * (G(i-1, j) + G(i+1, j) + G(i, j-1)
                                             + G(i, j+1)) + one_minus_omega * G(i, j);
                                                  }
