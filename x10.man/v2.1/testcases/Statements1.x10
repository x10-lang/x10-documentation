 package statements.should.be.called.commands.but.nobody.ever.does.that;
 class EmptyStatementExample {
 def summizmo (a:Rail[Int]!){
var sum: Int = 0;
for (var i: Int = 0; i < a.length; i++, sum += a(i))
    ;
}}