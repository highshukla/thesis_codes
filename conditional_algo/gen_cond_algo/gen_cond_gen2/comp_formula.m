L := SplittingField([Polynomial([-3,0,1]), Polynomial([-2,0,1])]);
Lx<x> := FunctionField(L);
k<t, s1, s2, s3, s4>:= FunctionField(L,5);
h := hom<k->Lx | [x,0,0,0,0]>;
p := -t^2;
s0 := p;
e := [-2*p, -p, 0, p, 2*p];
s := [s0,s1,s2,s3,s4];
val := [([e[j]^(2-i) : i in [0..2]] cat [-s[j]*e[j]^(1-i): i in [0..1]]): j in [1..5]];
M := Transpose(Matrix(k,5,5,val));

vec := Vector(k,5,[4*p^2*s0, s1*p^2, 0, s3*p^2, s4*4*p^2]);
sol := Solution(M, vec);
v2 := sol[1]; v1:=sol[2]; v0:= sol[3]; 
w1:= sol[4]; w0:= sol[5];
R0 := v0-v2*w0;
R1 := v1-v2*w1;
w := Polynomial([w0,w1,1]);
R := Polynomial([R0,R1]);

val := (e[1])^(-1)*(Evaluate(R, 0)* Evaluate(w, -2*p)/Evaluate(R, -2*p) - Evaluate(w,0));
num := Numerator(val);
den := Denominator(val);
sq2 := SquareRoot(L!2);
sq3 := SquareRoot(L!3);
sq := [1,sq2,sq3,2];
evalptinf :=  [t] cat [t*sq[i]*(1- 1/(2*i*p) - 1/(2*(2*i*p)^2)): i in [1..4]];
evalptp := [t] cat [t*sq[i]*(1- p/(2*i) - p^2/(2*(2*i)^2)): i in [1..4]];
val := Evaluate(val,evalptp);

val := h(val);
num := Numerator(val); den := Denominator(val);
cn := Coefficients(num); cd := Coefficients(den); 
value := cn[3]/cd[1];
value := (1-value)*(2-value);
value := 4*value/3; //the value is (L.1+1)*(3*L.1+1).
value;
IsUnit(value/sq2^3);
value := value/sq2^3;
U, m := UnitGroup(L);
value@@m;
element := ElementToSequence(value@@m);
ind := [i : i in [1..4]| element[i] mod 2 ne 0];
ind;
element:= -elt<L|m(U.3)>;
K := ext<Rationals()|MinimalPolynomial(element)>;

value := MinimalPolynomial((1+K.1)*K.1);
value;
for p in [1..1000000] do 
  if IsPrime(p) and (p+1) mod 48 eq 0 then 
    Fp := FiniteField(p); cp := [Fp!c : c in Coefficients(value)];
    val := Roots(Polynomial(cp))[1][1]; 
    assert IsSquare(val) ne false; 
  end if;
end for;



/*
C := ComplexField(50);
LtoC := hom<L-> C| SquareRoot(C!2)+SquareRoot(C!3)>;

cn := Coefficients(num); cd := Coefficients(den); cn := [LtoC(c): c in cn];
cd := [LtoC(d): d in cd];
num := Polynomial(cn); den := Polynomial(cd);
*/


/*
hilbsymbs := [**];
num;
den;

for q in [1..5000] do 
  if IsPrime(q) and (q+1) mod 24 eq 0 then 
Qp := pAdicField(q, 40);
Lp := ext<Qp| Polynomial([q,0,1])>;
LtoLp := hom<L-> Lp | SquareRoot(Lp!2)+SquareRoot(Lp!3)>;
pi := UniformizingElement(Lp); res := quo<IntegerRing(Lp)| pi>;
//nump := Polynomial([LtoLp(c): c in cn]); denp := Polynomial([LtoLp(c): c in cd]);
//value := Evaluate(nump, Lp.1)/Evaluate(denp, Lp.1);
value := LtoLp(cn[3]/cd[1]);
//value;
value := (1-value)*(2-value);
//value;
//value;
value := res!value;
value := Integers()!value mod q;
Append(~hilbsymbs, <q,HilbertSymbol(value, -q, q) >);
  end if; end for;
*/
