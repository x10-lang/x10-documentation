


finish {
ateach ([p]: Point in U) {
var ilow: int;


if (U(p).isFirst()) {
ilow = 1;
} else {
ilow = 0;
}
for ([n,i]: Point in testArray.dist| here) {
if (i >= ilow) {


// Calculate A[i] terms. Note, once again, that we
// can ignore the 2/period term outside the integral
// since the period is 2 and the term cancels itself
// out.
if (n == 0) {
testArray(0, i) = TrapezoidIntegrate(0.0 as double,
2.0 as double,
1000,
omega * i as double,
1);                       // 1 = cosine term.
} else {
// Calculate the B[i] terms.


testArray(n, i) = TrapezoidIntegrate(0.0 as double,
2.0 as double,
1000,
omega * i as double,
2);                       // 2 = sine term.
}
}
}
}
}

