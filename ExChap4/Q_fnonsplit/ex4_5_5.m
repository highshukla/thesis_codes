load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/is_good_elt.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/example.m";
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(QQ);
f := (x-179)*(x^4-179^2)*(x^2-2*179);
C := HyperellipticCurve(f);
J := Jacobian(C);
SG, SGtoA := TwoSelmerGroup(J);
AtoSG := invert_SGtoA(SGtoA);
A := Codomain(SGtoA);
tests := goodness_tests(SGtoA);
elt1 := -1241/1009483746*A.1^6 + 43/192246*A.1^5 - 923/1879858*A.1^4 - 11/358*A.1^3 
        + 8497/15753*A.1^2 - 32/3*A.1 + 552573/5251;


elt2 := -341083/6505113259224*A.1^6 + 1/128164*A.1^5 + 1254931/4542676857*A.1^4 +
1/716*A.1^3 - 3912227/203024664*A.1^2 - 1/2*A.1 - 4027285/567108;


printf "elt1 corresponds to the tuple %o in representation of Etale algebra as product of fields", <Evaluate(elt1,x) mod e[1]: e in Factorization(f)>;
printf "elt2 corresponds to the tuple %o in representation of Etale algebra as product of fields",<Evaluate(elt2,x) mod e[1]: e in Factorization(f)>;


/*for g in SG do 
[Evaluate(SGtoA(g),x) mod e[1]: e in Factorization(f)];
end for;
  */
print "Is elt1 good?";
print "Ans: ", forall{t: t in tests| t(AtoSG(elt1))};
ctpval := compctp(f, C, SGtoA, J, AtoSG(elt1), AtoSG(elt2));


