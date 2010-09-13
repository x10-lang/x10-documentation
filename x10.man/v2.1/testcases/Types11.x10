 package ch4;
class Cell[T] {
    var x: T;
    def this(x: T) { this.x = x; }
    def get(): T = x;
    def set(x: T) = { this.x = x; }
}