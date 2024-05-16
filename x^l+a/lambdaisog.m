//Qx<x> := PolynomialRing(Rationals());
//bound := 1000;
//l := 5;
function getA(bound,l)
	Al := [];
	Fl := GF(l);
	Kl := CyclotomicField(l);
	Ol := MaximalOrder(Kl);
	for A:= 4 to bound do
    if A ne SquareFree(A) then continue; end if;
		if A mod l eq 0 or IsSquare(Fl!A) then continue; end if;
    primes := PrimeDivisors(SquareFree(A));
		if 2 notin primes then Append(~primes, 2); end if;
		bad_places := &cat[[val[1] : val in Decomposition(Ol,p)] :  p in primes];
    test := [IsSquare(Completion(Kl,val)!A): val in bad_places];
    if exists{t : t in test | t eq true} then continue; end if;
		Append(~Al, A);
	end for;
	return Al;
end function;	
/*
Al := getA(bound, l);
for i in [1..#Al] do 
	SG := PhiSelmerGroup(x^2-Al[i], l);
	if Order(SG) eq l then 
		Remove(~Al, i);
	end if;
end for;
*/

//Z := Integers();
//P := Primes();
//l := 3;

//A := 13;
//S, m := PhiSelmerGroup(x^2-A, l);

//SG, m := PhiSelmerGroup(Polynomial([-23,0,Rationals()!1]),5);
//A := Domain(m);
//k := BaseField(A);
/*
k := CyclotomicField(5); zeta := k.1; assert zeta^5 eq 1;
L := ext<k| Polynomial([-23,0,1])>;
assert L.1^2 eq 23;
AtoL:= hom<A -> L | L.1>;
//d1 := AtoL(SG.1@@m); d2 := AtoL(SG.2@@m);
d1 := (-5*zeta^3 - 5*zeta^2)*L.1 - 10*zeta^3 - 10*zeta^2 + 21;
d2 := (5*zeta^3 + 5*zeta^2 + 5)*L.1 - 10*zeta^3 - 10*zeta^2 - 31;
d1, d2;

//d1,d2 for l=7 A=6
//d1 := (-183*zeta_7^5 + 240*zeta_7^4 + 240*zeta_7^3 - 183*zeta_7^2 + 313)*L.1 - 
    448*zeta_7^5 + 588*zeta_7^4 + 588*zeta_7^3 - 448*zeta_7^2 + 767;
//d2 :=(-185*zeta_7^5 - 281*zeta_7^4 - 281*zeta_7^3 - 185*zeta_7^2 + 104)*L.1 - 
    368*zeta_7^5 - 790*zeta_7^4 - 790*zeta_7^3 - 368*zeta_7^2 + 109;448*zeta_7^5 + 588*zeta_7^4 + 588*zeta_7^3 - 448*zeta_7^2 + 767;


K := ext<L| Polynomial([-d1,0,0,0,0,1])>;
assert Degree(K,L) eq 5;
assert K.1^5 eq d1;
print("Entering norm computation");
kl, emb := Completion(k, (1-zeta)*MaximalOrder(k): Precision:= 600);
kl := ChangePrecision(kl, 600);
ll := ext<kl|Polynomial([-23,0,1])>;
Ltoll := hom<L->ll| arg:-> kl!emb(y[1])+ll.1*(kl!emb(y[2])) where y := ElementToSequence(arg)>;
d1l := Ltoll(d1); d2l := Ltoll(d2);

//bool, c := NormEquation(K, 2*L.1);
c:= (1/505*(113794*zeta^3 - 81381*zeta^2 + 120615*zeta - 11033)*L.1 + 
        1/505*(546016*zeta^3 - 390192*zeta^2 + 578641*zeta - 52880))*K.1^4 + 
        (1/505*(-29334*zeta^3 - 14881*zeta^2 - 8961*zeta - 33059)*L.1 + 
        1/505*(-141252*zeta^3 - 71412*zeta^2 - 43010*zeta - 158646))*K.1^3 + 
        (1/505*(-833*zeta^3 + 5072*zeta^2 - 3565*zeta + 4536)*L.1 + 
        1/505*(-3405*zeta^3 + 24368*zeta^2 - 17216*zeta + 22388))*K.1^2 + 
        (1/505*(1347*zeta^3 + 63*zeta^2 + 768*zeta + 897)*L.1 + 
        1/505*(5762*zeta^3 - 772*zeta^2 + 4248*zeta + 3052))*K.1 + 
        1/505*(-224*zeta^3 - 623*zeta^2 - 87*zeta - 521)*L.1 + 
        1/505*(-936*zeta^3 - 457*zeta^2 - 1103*zeta - 644);

g := hom<K-> K| zeta*K.1>;
assert Norm(c) eq 2*L.1; assert &*[(g^i)(c): i in [0..4]] eq K!(2*L.1);
t1 := 1 + &+[((2*L.1)^i)/(&*[(g^j)(c): j in [0..i-1]])^5 : i in [1..4]];
assert t1 ne K!0;
assert t1/g(t1) eq 2*L.1/c^5;
nt1 := Numerator(t1); dt1 := Denominator(t1);
nc := Numerator(c); dc := Denominator(c);
primes := &join[SequenceToSet(PrimeDivisors(Min(v*MaximalOrder(K) meet 
Integers()))): v in [nt1,dt1,nc,dc]] diff  {2,5,23};
primes := SetToSequence(primes);
primesL := [Decomposition(MaximalOrder(L),p): p in primes];
primesL := [[x[1]: x in p]: p in primesL];
primesK := [[Decomposition(MaximalOrder(K),x): x in p ]:p in primesL];
primesK := [[[x[1]: x in pk]: pk in p]: p in primesK];
cideal := c*MaximalOrder(K); tideal := t1*MaximalOrder(K);
valc := [[[Valuation(cideal,x): x in pk]:pk in p]:p in primesK];
valt1 := [[[Valuation(tideal,x): x in pk]: pk in p] :p in primesK];
v1 := primesL[2][6]; v2 := primesL[3][1];
res1, m1 := ResidueClassField(MaximalOrder(L), v1);
res2, m2 := ResidueClassField(MaximalOrder(L), v2);
q1 := (primes[2]-1)/5; q2 := (primes[3]-1)/5;
w1 := m1(1/d2)^(Integers()!q1); w2 := m2(1/d2)^(Integers()!q2);
z1 := [m1(zeta^i): i in [1..5]]; z2 := [m2(zeta^i): i in [1..5]];
ctp := Index(z1,w1)+ Index(z2,w2) mod 5;
*/
