def reduce[T](in:DistArray[T], red:Reducible[T]) {
    val P = Place.MAX_PLACES;
    val phases = Utils.log2(P);
    val x = new DistArray[Clocked[T]](in.dist,
      (p:Point(in.rank))=>new ClockedAcc[T](in(p),in(p),red));
    clocked finish  {
    	for (p in x.dist.places()) clocked async at(p) {
    		var shift:Int=1;
    		for (phase in 0..phases-1) {
                        x((p.id+shift)%P)() <- x(p.id)();
    			shift *=2;
    			Clock.advanceAll();
    		}
    	}
    }
    return x(0)();
}