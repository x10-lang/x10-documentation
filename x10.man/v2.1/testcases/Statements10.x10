 package statements.are.from.mars.expressions.are.from.venus;
 class ThrowStatementExample {
 def thingie(i:Int, x:ValRail[Boolean]) throws MyIndexOutOfBoundsException {
if (i < 0 || i >= x.length)
    throw new MyIndexOutOfBoundsException();
} }
 class MyIndexOutOfBoundsException extends Exception {}