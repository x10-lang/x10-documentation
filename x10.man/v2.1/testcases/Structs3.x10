 package Structs.Pairs.Are.For.Squares;
struct Pair[T,U] {
    public val first:T;
    public val second:U;
    public def this(first:T, second:U):Pair[T,U] {
        this.first = first;
        this.second = second;
    }
    public  safe def toString():String {
        return "(" + first + ", " + second + ")";
    }
}
