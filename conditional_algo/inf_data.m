Qv := RealField(); Qvt := PolynomialRing(Qv); 
fv := Qvt!f;
Cv := BaseChange(C, Qv);
Jv := BaseChange(J, Qv);
gv := <Qv!d : d in g>;
gpv := <Qv!d : d in g>;
//E := ext<Qv| Qvt.1^2-11>;
//dp := <d: d in gpv| not IsSquare(d)>;


