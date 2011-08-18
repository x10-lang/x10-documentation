\begin{example}
\begin{lstlisting}
@det
def stencil(a:Array[Double], eps:Double, P:Int) {
    val red = Double.Reducible.max; 
    val err = new ClockedAcc[Double](Double.MAX_VALUE,
       Double.MAX_VALUE, red);
    val b = new Clocked[Array[Double](1)](
               new Array[Double](a.region, (p:Point(a.rank))=>0.0D);
               new Array[Double](a.region, (p:Point(a.rank))=>a(p)));

    clocked finish for (myRegion in b.region.partition(P))
        //method partitions a into P pieces.
        clocked async @Write(b() | myRegion) {
            while (err() > eps) {
                for (k in myRegion) {
                    val ck = (b()(k-1)+b()(k+1))/2;
                    err() <- Double.abs(ck - b()(k));
                    b()(k) = ck;
                }
                Clock.advanceAll();
            }
        }
    return b.finalized();
}
\end{lstlisting}
\end{example}