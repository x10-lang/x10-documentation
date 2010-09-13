 package Activities;
class OneBuffer[T] {
  var datum: T;
  var filled: Boolean = false;
  public def send(v: T) {
    when (!filled) {
      this.datum = v;
      this.filled = true;
    }
  }
  public def receive(): T {
    when (filled) {
      v: T = datum;
      filled = false;
      return v;
    }
  }
}
