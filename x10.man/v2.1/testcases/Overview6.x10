class List[T] {
    var head: T;
    var tail: List[T]!;
    def this(h: T, t: List[T]!) { head = h; tail = t; }
    def add(x: T) {
        if (this.tail == null)
            this.tail = new List(x, null);
        else
            this.tail.add(x);
    }
}