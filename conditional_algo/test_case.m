//load "/home/himanshu/dfg_proj/secondyear/conditional_algo/is_double.magma";
load "/home/himanshu/dfg_proj/secondyear/twoselmersetextra/search_fast_ms_org.m";

Qx := PolynomialRing(Rationals());
f := -10*(Qx.1-1)*(Qx.1-10)*(Qx.1-5)*(Qx.1)*(Qx.1+5)*(Qx.1+10);
PoBR := [2,3,11,5];
C := HyperellipticCurve(f);
b, C := HasOddDegreeModel(C);
C := convert_monic_integral(C);

J := Jacobian(C);
f := DefiningPolynomial(C);
f := -Evaluate(f,[Qx.1,0,1]);
flag, SG, TinSG, SSinSG, SStors, AtoSG, SGtoA, good, good_elts := is_good(C);
WPts := [r[1]: r in Roots(f)];
//good_elts[1] in SStors;
g := <Evaluate(SGtoA(good_elts[1]),w): w in WPts>;
gp := <Evaluate(SGtoA(good_elts[2]),w): w in WPts>;

Lx.1^5 - 25000*Lx.1^4 - 31250000*Lx.1^3 + 781250000000*Lx.1^2 + 156250000000000*Lx.1 -  3906250000000000000
