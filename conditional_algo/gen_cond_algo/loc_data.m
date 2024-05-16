

v :=5 ;

//the following part asks magma for a suggested precision which is high enough
//for computing factorizations and roots. 
Qv := pAdicField(v, 20); Qvt := PolynomialRing(Qv); prec := SuggestedPrecision(Qvt!f)+5;
Qv := ChangePrecision(Qv, prec); Qvt:= ChangeRing(Qvt,Qv); prec := SuggestedPrecision(Qvt!f)+5;
Qv := ChangePrecision(Qv, prec); Qvt := ChangeRing(Qvt, Qv); fv := Qvt!f;

Cv := BaseChange(C, Qv);
Jv := BaseChange(J, Qv);
gv := <Qv!d : d in g>;
gpv := <Qv!d : d in g>;
//E := ext<Qv| Qvt.1^2-11>;
dp := <d: d in gpv| not IsSquare(d)>;


