load "/home/himanshu/thesis_codes/ExChap5/PhiDescentStoll.m";
l:= 5;
a := 23;
print "This piece of code checks the claims of Section 5.6.2 on the cuve C_62";
print ""; print "";
print "Computing 1-zeta_l Selmer group for l, A: ",l, a;
SG, m, loc := getSelelts(l,a);
k := BaseField(Domain(m)); A := Domain(m); L:= ext<k|Polynomial([-a,0,1])>; 
AtoL := hom<A->L|L.1>; LtoA := hom<L-> A|A.1>;
Ltoll := LtoA*loc;
ll := Codomain(loc); kl := BaseField(ll);
zeta_5 := k.1;

d1 := (-5*zeta_5^3 - 5*zeta_5^2)*A.1 - 10*zeta_5^3 - 10*zeta_5^2 + 21;
d2 := (5*zeta_5^3 + 5*zeta_5^2 + 5)*A.1 - 10*zeta_5^3 - 10*zeta_5^2 - 31;

print "elements d_1, d_2: ", d1,d2;


print "Is d_1 an element of Selmer group?";
print "Ans: ", exists{g:g in SG| m(d1) eq g};

print ""; print "";
print "Is d_2 an element of Selmer group?";
print "Ans: ",exists{g:g in SG| m(d2) eq g};

print ""; print "";
print "Is d1/d2^4 is 5th power at lambda?";
print "Ans: ", IsPower(loc(d1)/loc(d2)^4,5);

print "";print "";
K := ext<L|Polynomial([-AtoL(d1),0,0,0,0,1])>; OK := MaximalOrder(K);
OL:= MaximalOrder(L);
d2 := AtoL(d2);
g := hom<K-> K| zeta_5*K.1>;

c:= (1/505*(113794*zeta_5^3 - 81381*zeta_5^2 + 120615*zeta_5 - 11033)*L.1 + 
        1/505*(546016*zeta_5^3 - 390192*zeta_5^2 + 578641*zeta_5 - 52880))*K.1^4 + 
        (1/505*(-29334*zeta_5^3 - 14881*zeta_5^2 - 8961*zeta_5 - 33059)*L.1 + 
        1/505*(-141252*zeta_5^3 - 71412*zeta_5^2 - 43010*zeta_5 - 158646))*K.1^3 + 
        (1/505*(-833*zeta_5^3 + 5072*zeta_5^2 - 3565*zeta_5 + 4536)*L.1 + 
        1/505*(-3405*zeta_5^3 + 24368*zeta_5^2 - 17216*zeta_5 + 22388))*K.1^2 + 
        (1/505*(1347*zeta_5^3 + 63*zeta_5^2 + 768*zeta_5 + 897)*L.1 + 
        1/505*(5762*zeta_5^3 - 772*zeta_5^2 + 4248*zeta_5 + 3052))*K.1 + 
        1/505*(-224*zeta_5^3 - 623*zeta_5^2 - 87*zeta_5 - 521)*L.1 + 
        1/505*(-936*zeta_5^3 - 457*zeta_5^2 - 1103*zeta_5 - 644);

print "Is Norm(c) equal to 2*sqrt{A}?";    
print "Ans: ", Norm(c) eq 2*L.1; &*[(g^i)(c): i in [0..4]] eq K!(2*L.1);
print ""; print "";

t1 := 1 + &+[((2*L.1)^i)/(&*[(g^j)(c): j in [0..i-1]])^5 : i in [1..4]];
print "Value of t: ",1/t1;
assert t1 ne K!0;
assert t1/g(t1) eq 2*L.1/c^5;
tideal := OK*t1;
cideal := OK*c;
nt1 := Numerator(t1); dt1 := Denominator(t1);
nc := Numerator(c); dc := Denominator(c);
primes := &join[SequenceToSet(PrimeDivisors(Min(v*MaximalOrder(K) meet 
Integers()))): v in [nt1,dt1,nc,dc]]; 
print ""; print "";
print "Rational primes below primes dividing t: ", primes;
print ""; print "";
print "Remove the primes {2,5,23}", primes diff {2,5,23};
primes := primes diff {2,5,23};
primes := SetToSequence(primes);
primesL := [Decomposition(MaximalOrder(L),p): p in primes];
primesL := [[x[1]: x in p]: p in primesL];
primesK := [[Decomposition(OK,x): x in p ]:p in primesL];
primesK := [[[x[1]: x in pk]: pk in p]: p in primesK];
valc := [[[Valuation(cideal,x): x in pk]:pk in p]:p in primesK];
valt1 := [[[Valuation(tideal,x): x in pk]: pk in p] :p in primesK];
print "Valuations of primes of K above the above primes at c: ", valc;
print ""; print "";
print "Valuations of primes of K above the above primes at t: ", valt1;
delta_glob := t1*(&*[(g^i)(c^(l-1-i)): i in [0..l-2]]);
print "";print "";
print "Value of delta_glob: ",delta_glob;

v1 := primesL[1][4]; res1, m1 := ResidueClassField(MaximalOrder(L),v1);
valdelglob := Valuation(delta_glob*OK,primesK[1][4][1]);
print "Valuation at the relavant prime above 101 of delta_glob: ",
valdelglob;
q1 := (primes[1]-1)/5; w1 := m1(d2)^(Integers()!q1); 
z1 := [m1(zeta_5^i): i in [1..5]];
ctp := (Index(z1,w1)*valdelglob) mod 5;
print "Value of CTP: ", ctp/5;
