package Vars.For.Bears.In.Chairs;
class VarExample{
static def example() {
val a : Int = 0;               // Full 'val' syntax
b : Int = 0;                   // 'val' implied
val c = 0;                     // Type inferred
var d : Int = 0;               // Full 'var' syntax
var e : Int;                   // Not initialized
var f : Int{self != 100} = 0;  // Constrained type
}}