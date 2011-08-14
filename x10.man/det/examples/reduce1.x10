def reduce[T](in:DistArray[T], red:Reducible[T]) {
    val acc = new Acc[T](red);
    finish for (dest in in.dist.places())
        async
            at (dest) 
               for (p in dist | here)
                 acc <- in(p);
    return acc();
}