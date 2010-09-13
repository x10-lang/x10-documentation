 package Structs.For.Muckts;
struct Pair[T,U](t:T, u:U) {
  def this(t:T, u:U) { property(t,u); }
  def diag(){T==U && t==u} = t;
}
