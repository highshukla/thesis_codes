l := 5;
a := 62;
SG, m, loc := getSelelts(l,a);
k := BaseField(Domain(m)); A := Domain(m); L:= ext<k|Polynomial([-a,0,1])>; 
AtoL := hom<A->L|L.1>; LtoA := hom<L-> A|A.1>;
Ltoll := LtoA*loc;
ll := Codomain(loc); kl := BaseField(ll);
zeta_5 := k.1;
d1 := -4*A.1 - 32;
d2:= (-74*zeta_5^3 - 74*zeta_5^2 - 38)*A.1 - 7*zeta_5^3 - 7*zeta_5^2 - 655;
K := ext<L|Polynomial([-AtoL(d1),0,0,0,0,1])>; OK := MaximalOrder(K);
OL:= MaximalOrder(L);
d2 := AtoL(d2);
g := hom<K-> K| zeta_5*K.1>;
c:=(1/20*(zeta_5^3 + 8*zeta_5^2 + zeta_5)*L.1 + 1/20*(8*zeta_5^3 - 55*zeta_5^2 - 
    4*zeta_5 + 14))*K.1^4 + (1/20*(-7*zeta_5^3 - 6*zeta_5^2 - 6*zeta_5 - 9)*L.1 
    + 1/10*(11*zeta_5^3 + 30*zeta_5^2 + 15*zeta_5 + 31))*K.1^3 + 
    (1/10*(-zeta_5^3 - 3*zeta_5^2 + zeta_5 - 1)*L.1 + 1/10*(-13*zeta_5^3 - 
    9*zeta_5^2 - 7*zeta_5 - 22))*K.1^2 + (1/10*(7*zeta_5^3 + 3*zeta_5^2 + 
    3*zeta_5 + 6)*L.1 + 1/5*(28*zeta_5^3 - 9*zeta_5^2 + 7*zeta_5 + 9))*K.1 + 
    1/5*(-2*zeta_5^3 + 5*zeta_5^2 - 3*zeta_5 + 1)*L.1 + 1/5*(-13*zeta_5^3 + 
    35*zeta_5^2 - 14*zeta_5 + 23);
assert Norm(c) eq 2*L.1; assert &*[(g^i)(c): i in [0..4]] eq K!(2*L.1);
//t1 := 1 + &+[((2*L.1)^i)/(&*[(g^j)(c): j in [0..i-1]])^5 : i in [1..4]];
    t1:= (1/153760*(-31830784548028035*zeta_5^3 - 8519841930815387*zeta_5^2 - 
    14407000621397824*zeta_5 - 28192312761404049)*L.1 + 
    1/153760*(-250635543414515120*zeta_5^3 - 67085234320889830*zeta_5^2 - 
    113440339035289028*zeta_5 - 221986739280518733))*K.1^4 + 
    (1/153760*(-64619034657274574*zeta_5^3 + 4457205341736792*zeta_5^2 - 
    42691533278345214*zeta_5 - 35479528178252173)*L.1 + 
    1/76880*(-254405497946715677*zeta_5^3 + 17548159824886515*zeta_5^2 - 
    168076749834627462*zeta_5 - 139682829514521585))*K.1^3 + 
    (1/76880*(-40745449123285363*zeta_5^3 + 37879263130489315*zeta_5^2 - 
    48592753823880416*zeta_5 + 12697254382901017)*L.1 + 
    1/76880*(-320830006425518370*zeta_5^3 + 298261357370151860*zeta_5^2 - 
    382619780134954978*zeta_5 + 99978121244912765))*K.1^2 + 
    (1/76880*(29249628130171194*zeta_5^3 + 112355600925041064*zeta_5^2 - 
    51362266731043416*zeta_5 + 130432990350372375)*L.1 + 
    1/38440*(115155927142019301*zeta_5^3 + 442344537736112267*zeta_5^2 - 
    202213482025571708*zeta_5 + 513515218748741515))*K.1 + 
    1/38440*(149447795611735665*zeta_5^3 + 127777323457892605*zeta_5^2 + 
    13393201479259730*zeta_5 + 220141194742341683)*L.1 + 
    1/38440*(1176753128489333010*zeta_5^3 + 1006119635851234270*zeta_5^2 + 
    105458261911696660*zeta_5 + 1733393497347883443);
assert t1 ne K!0;
assert t1/g(t1) eq 2*L.1/c^5;

tideal := OK*t1;
primes :=SequenceToSet(PrimeDivisors(Min(tideal meet Integers())));
primes := SetToSequence(primes);
primesL := [Decomposition(MaximalOrder(L),p): p in primes];
primesL := [[x[1]: x in p]: p in primesL];
primesK := [[Decomposition(MaximalOrder(K),x): x in p ]:p in primesL];
primesK := [[[x[1]: x in pk]: pk in p]: p in primesK];
valt1 := [[[Valuation(tideal,x): x in pk]: pk in p] :p in primesK];
v1:= primesL[1][3]; v2 := primesL[2][1]; v3 := primesL[3][6]; 
res1, m1 := ResidueClassField(OL, v1);
res2, m2 := ResidueClassField(OL, v2);
res3, m3 := ResidueClassField(OL, v3);

q1 := (primes[1]-1)/5; q2 := (primes[2]-1)/5; q3 := (primes[3]-1)/5;
w1 := m1(d2)^(Integers()!q1); w2 := m2(d2)^(Integers()!q2);
w3 := m3(d2)^(Integers()!q3); 
z1 := [m1(zeta_5^i): i in [1..5]]; z2 := [m2(zeta_5^i): i in [1..5]];
z3 := [m3(zeta_5^i): i in [1..5]]; 
ctp := (Index(z1,w1)+ Index(z2,w2) + Index(z3,w3)) mod 5;
defpolK := DefiningPolynomial(K);
assert Evaluate(defpolK, K.1) eq 0;
r := Roots(Polynomial([-loc(d1),0,0,0,0,1]))[1][1];
Ktoll := hom<K-> ll| x:-> &+[Ltoll(y[i])*r^(i-1) where y := ElementToSequence(x): i in
  [1..#ElementToSequence(x)]]>;
Sd2 := SplittingField(Polynomial([-Ltoll(d2),0,0,0,0,1]));
U, mu := UnitGroup(ll);
l1 := Decomposition(OK, (1-zeta_5)*OL)[1][1];
bool := NormEquation(Sd2, mu, Ktoll(t1));
assert bool eq true;

