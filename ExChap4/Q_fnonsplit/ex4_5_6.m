load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/is_good_elt.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/example.m";
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(QQ);
f := x*(x^3-107)*(x^3-2*107);
C := HyperellipticCurve(f);
J := Jacobian(C);
SG, SGtoA := TwoSelmerGroup(J);
AtoSG := invert_SGtoA(SGtoA);
A := Codomain(SGtoA);
tests := goodness_tests(SGtoA);
elt1 := -21/22898*A.1^6 + 1/107*A.1^5 - 2/107*A.1^4 + 21/214*A.1^3 - A.1^2 + 2*A.1 + 1;


elt2 := 11/22898*A.1^6 - 2/107*A.1^4 - 11/214*A.1^3 + 2*A.1 + 1;

//Factorization(f);
printf "elt1 corresponds to the tuple %o in representation of Etale algebra as product of fields", <Evaluate(elt1,x) mod e[1]: e in Factorization(f)>;
printf "elt2 corresponds to the tuple %o in representation of Etale algebra as product of fields",<Evaluate(elt2,x) mod e[1]: e in Factorization(f)>;


/*
for g in SG do 
[Evaluate(SGtoA(g),x) mod e[1]: e in Factorization(f)];
end for;
*/
print "Is elt1 good?";
print "Ans: ", forall{t: t in tests| t(AtoSG(elt1))};
ctpval := compctp(f, C, SGtoA, J, AtoSG(elt1), AtoSG(elt2));


