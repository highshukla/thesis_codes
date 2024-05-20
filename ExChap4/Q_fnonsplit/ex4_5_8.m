load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/is_good_elt.m";
load "/home/himanshu/thesis_codes/ExChap4/Q_fnonsplit/example.m";
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(QQ);
f := (x-137)*(x^4-137^2)*(x^4-4*137^2);
C := HyperellipticCurve(f);
J := Jacobian(C);
SG, SGtoA := TwoSelmerGroup(J);
AtoSG := invert_SGtoA(SGtoA);
A := Codomain(SGtoA);
tests := goodness_tests(SGtoA);
elt1 := -1/195865100716*x^8 + 1/10285412*x^6 - 273/10435564*x^4 - 1/548*x^2 + 415/278;


elt2 := 11413/21153430877328*x^8 - 1/15428118*x^7 - 17/15428118*x^6 - 4/56307*x^5 + 
    7889287/1127040912*x^4 + 1/822*x^3 + 17/822*x^2 + 13/3*x - 8145107/15012;

//Factorization(f);
printf "elt1 corresponds to the tuple %o in representation of Etale algebra as product of fields", <Evaluate(elt1,x) mod e[1]: e in Factorization(f)>;
printf "elt2 corresponds to the tuple %o in representation of Etale algebra as product of fields",<Evaluate(elt2,x) mod e[1]: e in Factorization(f)>;
/*for g in SG do 
[Evaluate(SGtoA(g),x) mod e[1]: e in Factorization(f)];
end for;
  */
print "Is elt1 good?";
print "Ans: ", forall{t: t in tests| t(AtoSG(elt1))};
ctpval := compctp(f, C, SGtoA, J, AtoSG(elt1), AtoSG(elt2));


