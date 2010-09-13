 import x10.util.*;
 class TypeDefNonGenerative {
 def someTypeDefs () {
type A = Int;
type B = String;
type C = String;
a: A = 3;
b: B = new C("Hi");
c: C = b + ", Mom!";
 }}